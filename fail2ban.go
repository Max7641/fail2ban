package main

import (
	"bufio"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/fsnotify/fsnotify"
)

/*
主线程启动event select线程，event select线程捕获到事件后处理事件，
当为修改事件时发送给主线程命令，其他事件则重新注册监听，并重置offset
主线程也启动一个被ban ip的超时剔除线程，加锁修改各变量，剔除后发deban命令给主线程
主线程启动各子线程后进入命令管道处理循环，当modify事件来了，就打开文件，读取最新数据，依次进行匹配，
匹配成功则起一个线程处理结果

主线程加载配置，准备规则，初始化，启动event捕获线程，启动文件读取线程，超期ban解封线程
event捕获到创建，重命名，移动事件后，重新注册监听，若文件不存在，则一直等待，直到存在
若为文件修改，则通知文件读取线程进行读取匹配，同时更新offset
若匹配成功，则发送命令给主线程，主线程主线程负责操作防火墙，发送消息


*/
func ReadConfig(iniPath string) map[string]map[string]string {
	config := make(map[string]map[string]string)
	section := ""
	fr, err := os.Open(iniPath)
	if err != nil {
		log.Fatal(err)
	}
	defer fr.Close()
	r := bufio.NewReader(fr)
	for {
		line, err := r.ReadString('\n')
		if err != nil {
			if err == io.EOF {
				break
			}
			log.Fatal(err)
		}
		line = strings.TrimSpace(line)
		// 忽略空行
		if line == "" {
			continue
		}
		// 忽略注释行
		if strings.Index(line, "#") == 0 {
			continue
		}
		n1 := strings.Index(line, "[")
		n2 := strings.LastIndex(line, "]")
		if n1 == 0 && n2 > 1 {
			section = strings.TrimSpace(line[1:n2])
			config[section] = make(map[string]string)
			continue
		}
		// section如果为空就pass，直到有值
		if len(section) == 0 {
			continue
		}
		// 获取键值对
		index := strings.Index(line, "=")
		if index <= 0 {
			continue
		}
		key := strings.TrimSpace(line[:index])
		if len(key) == 0 {
			continue
		}
		value := strings.TrimSpace(line[index+1:])
		// 去掉值中的注释
		// pos := strings.Index(value, "#")
		// if pos > -1 {
		// 	value = value[0:pos]
		// }
		if len(value) == 0 {
			continue
		}
		// log.Println(section, key, value)
		config[section][key] = value
	}
	return config
}

func checkErr(err error) {
	if err != nil {
		log.Fatal(err)
	}
}

type rePattern struct {
	reType  string
	reDesc  string
	pattern *regexp.Regexp
}

type fail2ban struct {
	filePath        string               // 目标文件路径
	fileOffset      int64                // 目标文件当前偏移
	watcher         *fsnotify.Watcher    // 监听器
	cmdChan         chan [3]string       // 主线程命令通道(带缓冲) [类型，描述，ip]
	readFileChan    chan bool            // 文件读取触发通道，带缓存
	rePatternList   []*rePattern         // 正则匹配队列
	tryTimeOut      int64                // 尝试时间
	banTime         int64                // 被ban多久
	sleepTime       time.Duration        // 检测间隔
	tryTimes        int64                // 尝试次数
	lock            *sync.Mutex          // 同步锁
	tryIP           map[string]*[2]int64 // 尝试字典 {ip:[timestamp,count]}
	bannedIP        map[string]int64     // 已被ban的ip字典{ip:timestamp}
	dd_access_token string               // 钉钉token
	dd_secret       string               // 钉钉secret
	dd_header       string               // 钉钉消息头，用来区分告警来源
	httpClient      *http.Client         // 消息发送客户端
}

// 传入配置map，进行初始化,结构体内遍历可以直接赋值
func (f *fail2ban) init(config *map[string]map[string]string) {
	log.Println("init")
	var err error
	f.filePath = (*config)["main"]["filePath"]
	tryTimeOut, err := strconv.Atoi((*config)["main"]["tryTimeOut"])
	checkErr(err)
	f.tryTimeOut = int64(tryTimeOut)
	banTime, err := strconv.Atoi((*config)["main"]["banTime"])
	checkErr(err)
	f.banTime = int64(banTime)
	tryTimes, err := strconv.Atoi((*config)["main"]["tryTimes"])
	checkErr(err)
	f.tryTimes = int64(tryTimes)
	f.sleepTime = time.Second * 10
	watcher, err := fsnotify.NewWatcher()
	checkErr(err)
	f.watcher = watcher
	f.cmdChan = make(chan [3]string, 10)
	f.readFileChan = make(chan bool, 10)
	f.lock = new(sync.Mutex)
	f.tryIP = make(map[string]*[2]int64)
	f.bannedIP = make(map[string]int64)
	// 钉钉
	f.dd_access_token = (*config)["dingding"]["access_token"]
	f.dd_secret = (*config)["dingding"]["secret"]
	f.dd_header = (*config)["dingding"]["header"]
	f.httpClient = new(http.Client)
	f.httpClient.Timeout = time.Second * 10
	// 检查
	if f.filePath == "" || f.dd_access_token == "" || f.dd_secret == "" || f.dd_header == "" {
		log.Fatal("filePath or access_token or secret or header is empty!")
	}
	// 初始化pattern
	f.rePatternList = []*rePattern{}
	for k, v := range *config {
		if strings.Index(k, "re_") == 0 {
			rep := new(rePattern)
			rep.reType = v["type"]
			rep.reDesc = v["desc"]
			p, e := regexp.Compile(v["pattern"])
			if e == nil {
				rep.pattern = p
				f.rePatternList = append(f.rePatternList, rep)
				// log.Println(rep.reType, rep.reDesc, rep.pattern.String(), v["pattern"])
			}
		}
	}
	if len(f.rePatternList) == 0 {
		log.Fatal("未找到正则匹配规则！")
	}
}

// 关闭监听
func (f *fail2ban) close() {
	log.Println("close watcher")
	f.watcher.Close()
}

// 添加文件监听，直到文件存在
func (f *fail2ban) addFile() {
	log.Println("add file", f.filePath)
	for {
		i, err := os.Stat(f.filePath)
		if os.IsNotExist(err) {
			log.Println(f.filePath, "not exist!")
			time.Sleep(time.Second)
		} else {
			f.fileOffset = i.Size()
			f.watcher.Add(f.filePath)
			break
		}
	}
}

// 事件处理函数，由事件选择线程调用，处理重新注册及发送read消息给文件读取线程
func (f *fail2ban) eventDeal(e *fsnotify.Event) {
	// 处理消息，如果是新增，重命名，删除，则重新注册文件，若文件不存在，则一直等待
	// 若为修改事件，
	if e.Op&fsnotify.Write == fsnotify.Write {
		f.readFileChan <- true
	} else if e.Op&fsnotify.Create == fsnotify.Create || e.Op&fsnotify.Remove == fsnotify.Remove || e.Op&fsnotify.Rename == fsnotify.Rename {
		// 先Remove，再判断文件是否存在，存在则add，否则sleep
		log.Println(e.Name, "重新注册")
		f.watcher.Remove(f.filePath)
		f.addFile()
	} else {
		log.Println(e.Name)
	}
}

// 事件选择线程，调用事件处理函数对时间进行处理
func (f *fail2ban) eventSelect() {
	log.Println("eventSelect start")
	for {
		select {
		case event, ok := <-f.watcher.Events:
			if !ok {
				// 发送结束消息给主线程
				log.Println("chan Events closed!")
				f.cmdChan <- [...]string{"exit", "", ""}
				return
			}
			// 处理消息
			f.eventDeal(&event)
		case err, ok := <-f.watcher.Errors:
			if !ok {
				// 发送结束消息给主线程
				log.Println("chan Errors closed!")
				f.cmdChan <- [...]string{"exit", "", ""}
				return
			}
			log.Println("error:", err)
		}
	}
}

// 出狱检测线程
func (f *fail2ban) outBanCheck() {
	// 先拿锁，遍历，计算时间，若已经到期，则从字典中去除，然后发送命令给主线程
	log.Println("outBanCheck start")
	for {
		time.Sleep(f.sleepTime)
		f.lock.Lock()
		currTimeStamp := time.Now().Unix()
		// try的检测超时
		timeoutIP := []string{}
		for ip, t := range f.tryIP {
			if currTimeStamp-(*t)[0] > f.tryTimeOut {
				timeoutIP = append(timeoutIP, ip)
			}
		}
		for _, ip := range timeoutIP {
			delete(f.tryIP, ip)
		}
		// 被ban的出狱
		timeoutIP = []string{}
		for ip, t := range f.bannedIP {
			if currTimeStamp-t > f.banTime {
				timeoutIP = append(timeoutIP, ip)
			}
		}
		for _, ip := range timeoutIP {
			delete(f.bannedIP, ip)
			f.cmdChan <- [...]string{"deban", "", ip}
		}
		f.lock.Unlock()
	}
}

// 文件读取正则匹配线程
func (f *fail2ban) reReadFile() {
	log.Println("reReadFile start")
	for range f.readFileChan {
		// 打开文件，跳转到offset，按行读取直到eof，依次进行re匹配，成功则发消息给主线程
		// eof后，获取最新offset
		fr, _ := os.Open(f.filePath)
		fr.Seek(f.fileOffset, os.SEEK_SET)
		r := bufio.NewReader(fr)
		isEOF := false
		for {
			buf, err := r.ReadBytes('\n') //通过源码得到的返回值的个数和类型
			if err != nil {
				if err == io.EOF {
					isEOF = true
				} else {
					log.Fatal(err)
					break
				}
			}
			// 对行进行正则匹配
			// log.Println(string(buf))
			for _, p := range f.rePatternList {
				r := p.pattern.FindSubmatch(buf)
				if len(r) > 0 {
					// 匹配成功，获取分组内容后发给主进程
					// log.Println(string(r[0]), string(r[1]))
					f.cmdChan <- [...]string{p.reType, p.reDesc, string(r[1])}
					break
				}
			}
			if isEOF {
				curOffset, _ := fr.Seek(0, os.SEEK_CUR)
				f.fileOffset = curOffset
				break
			}
		}
		fr.Close()
	}
}

func (f *fail2ban) sendMsg(cmd *[3]string) {
	// [type,desc,ip]
	atAll := false
	now := time.Now().Format("2006-01-02 15:04:05")
	msg := fmt.Sprintf("【%s】\n%s\n%s %s", f.dd_header, now, (*cmd)[2], (*cmd)[1])
	if (*cmd)[0] == "ban" {
		atAll = true
	}
	// 生成url参数
	timestamp := fmt.Sprintf("%d", time.Now().UnixNano()/1000000)
	string_to_sign := fmt.Sprintf("%s\n%s", timestamp, f.dd_secret)
	mac := hmac.New(sha256.New, []byte(f.dd_secret))
	mac.Write([]byte(string_to_sign))
	b64 := base64.StdEncoding.EncodeToString(mac.Sum(nil))
	sign := url.QueryEscape(b64)
	params := url.Values{}
	params.Set("access_token", f.dd_access_token)
	params.Set("timestamp", timestamp)
	params.Set("sign", sign)
	url := "https://oapi.dingtalk.com/robot/send?" + params.Encode()
	content := make(map[string]interface{})
	content["msgtype"] = "text"
	content["text"] = map[string]string{"content": msg}
	if atAll {
		content["at"] = map[string]bool{"isAtAll": true}
	}
	pjson, err := json.Marshal(content)
	if err != nil {
		log.Println(err)
		return
	}
	req, _ := http.NewRequest("POST", url, strings.NewReader(string(pjson)))
	req.Header.Set("Content-Type", "application/json")
	rep, err := f.httpClient.Do(req)
	if err != nil {
		log.Println(err)
		return
	}
	defer rep.Body.Close()
	result := make(map[string]interface{})
	err = json.NewDecoder(rep.Body).Decode(&result)
	if err != nil {
		log.Println(err)
		return
	}
	// map[errcode:0 errmsg:ok]
	if result["errcode"].(float64) != 0 {
		log.Println(result["errmsg"])
	}
}

func (f *fail2ban) action(t string, ip string) {
	rule := fmt.Sprintf(`rule family=ipv4 source address="%s" drop`, ip)
	if t == "ban" {
		err := exec.Command("firewall-cmd", "--add-rich-rule", rule).Run()
		if err != nil {
			log.Println(err)
		}
	} else if t == "deban" {
		err := exec.Command("firewall-cmd", "--remove-rich-rule", rule).Run()
		if err != nil {
			log.Println(err)
		}
	} else {
		log.Println("unknow action:", t, ip)
	}
}

// 主线程，启动其他线程，处理防火墙及消息的发送
func (f *fail2ban) run() {
	f.addFile()
	// 启动子线程监听事件
	go f.eventSelect()
	//启动deban线程
	go f.outBanCheck()
	// 文件读取线程
	go f.reReadFile()
	// 阻塞到命令管道
	for cmd := range f.cmdChan {
		// [type,desc,ip]
		if cmd[0] == "ban" {
			f.lock.Lock()
			currTimeStamp := time.Now().Unix()
			if _, ok := f.bannedIP[cmd[2]]; ok {
				// 当大规模并行爆破时可能会被ban多次
				log.Println(cmd[2], "alread banned")
			} else {
				if t, ok := f.tryIP[cmd[2]]; ok {
					// 在try中, 超过重试次数则ban，否则count+1 {ip:[timestamp,count]}
					// 这里时间戳不应该更新，保持第一次时间，如果超时会被剔除掉
					if (*t)[1] >= f.tryTimes {
						delete(f.tryIP, cmd[2])
						f.bannedIP[cmd[2]] = currTimeStamp
						go f.sendMsg(&cmd)
						f.action(cmd[0], cmd[2])
						log.Println(cmd[2], "is banned")
					} else {
						(*f.tryIP[cmd[2]])[1]++
						log.Println(cmd[2], "try", (*f.tryIP[cmd[2]])[1], "times")
					}
				} else {
					// 不再try中，加入
					f.tryIP[cmd[2]] = &[2]int64{currTimeStamp, 1}
					log.Println(cmd[2], "try", 1, "times")
				}
			}
			f.lock.Unlock()
		} else if cmd[0] == "deban" {
			f.action(cmd[0], cmd[2])
			log.Println(cmd[2], "deban")
		} else {
			// info
			go f.sendMsg(&cmd)
		}
	}
}

func main() {
	workDir, _ := filepath.Abs(filepath.Dir(os.Args[0]))
	log.Println(workDir)
	os.Chdir(workDir)
	// 加载配置
	config := ReadConfig("fail2ban.ini")
	// log.Println(config)
	f := new(fail2ban)
	f.init(&config)
	go f.run()
	// 捕获信号量
	sigs := make(chan os.Signal, 1)
	signal.Notify(sigs, syscall.SIGINT, syscall.SIGTERM)
	<-sigs
	f.close()
	log.Println("exit")
}
