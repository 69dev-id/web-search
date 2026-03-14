package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"
)

type SearchState struct {
	mu        sync.Mutex
	paused    bool
	cancelled bool
	results   []string
	running   bool
}

var state = &SearchState{}

type SearchRequest struct {
	Query     string `json:"query"`
	Directory string `json:"directory"`
	MaxResult int    `json:"max_result"`
}

type SSEEvent struct {
	Type    string `json:"type"`
	Data    string `json:"data"`
	Count   int    `json:"count"`
	Elapsed string `json:"elapsed"`
}

func enableCORS(w http.ResponseWriter) {
	w.Header().Set("Access-Control-Allow-Origin", "*")
	w.Header().Set("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
	w.Header().Set("Access-Control-Allow-Headers", "Content-Type")
}

func sendSSE(w http.ResponseWriter, event SSEEvent) {
	data, _ := json.Marshal(event)
	fmt.Fprintf(w, "data: %s\n\n", string(data))
	if f, ok := w.(http.Flusher); ok {
		f.Flush()
	}
}

func searchHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	// Parse params
	query := r.URL.Query().Get("query")
	directory := r.URL.Query().Get("directory")
	maxStr := r.URL.Query().Get("max")
	if query == "" {
		http.Error(w, "query required", 400)
		return
	}
	if directory == "" {
		directory = `C:\Users\rdp\Desktop\backup\X-LOGS-main\ulp\downloads`
	}
	maxResult := 10000
	if maxStr != "" {
		if v, err := strconv.Atoi(maxStr); err == nil {
			maxResult = v
		}
	}

	// SSE headers
	w.Header().Set("Content-Type", "text/event-stream")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("Connection", "keep-alive")
	enableCORS(w)

	state.mu.Lock()
	if state.running {
		state.mu.Unlock()
		sendSSE(w, SSEEvent{Type: "error", Data: "Search already running"})
		return
	}
	state.running = true
	state.paused = false
	state.cancelled = false
	state.results = []string{}
	state.mu.Unlock()

	defer func() {
		state.mu.Lock()
		state.running = false
		state.mu.Unlock()
	}()

	startTime := time.Now()

	// Build ugrep command
	args := []string{
		"-r", "-F", "-J", "32", "-i", "-I",
		fmt.Sprintf("-m %d", maxResult),
		"--no-filename", "--no-messages",
		query,
		directory,
	}
	// Rebuild args properly
	args = []string{
		"-r", "-F", "-J", "32", "-i", "-I",
		"-m", strconv.Itoa(maxResult),
		"--no-filename", "--no-messages",
		query,
		directory,
	}

	cmd := exec.Command("ugrep", args...)
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		sendSSE(w, SSEEvent{Type: "error", Data: "Failed to start ugrep: " + err.Error()})
		return
	}

	sendSSE(w, SSEEvent{Type: "start", Data: fmt.Sprintf("Searching for: %s", query)})

	if err := cmd.Start(); err != nil {
		sendSSE(w, SSEEvent{Type: "error", Data: "ugrep not found. Please install ugrep first."})
		return
	}

	count := 0
	scanner := bufio.NewScanner(stdout)
	scanner.Buffer(make([]byte, 1024*1024), 1024*1024)

	for scanner.Scan() {
		// Check cancelled
		state.mu.Lock()
		cancelled := state.cancelled
		state.mu.Unlock()
		if cancelled {
			cmd.Process.Kill()
			break
		}

		// Handle pause
		for {
			state.mu.Lock()
			paused := state.paused
			state.mu.Unlock()
			if !paused {
				break
			}
			time.Sleep(100 * time.Millisecond)
		}

		line := scanner.Text()
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		count++
		elapsed := time.Since(startTime).Round(time.Millisecond).String()

		state.mu.Lock()
		state.results = append(state.results, line)
		state.mu.Unlock()

		sendSSE(w, SSEEvent{
			Type:    "result",
			Data:    line,
			Count:   count,
			Elapsed: elapsed,
		})
	}

	cmd.Wait()
	elapsed := time.Since(startTime).Round(time.Millisecond).String()

	state.mu.Lock()
	cancelled := state.cancelled
	state.mu.Unlock()

	if cancelled {
		sendSSE(w, SSEEvent{Type: "cancelled", Data: "Search cancelled", Count: count, Elapsed: elapsed})
	} else {
		sendSSE(w, SSEEvent{Type: "done", Data: fmt.Sprintf("Search complete"), Count: count, Elapsed: elapsed})
	}
}

func pauseHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	state.mu.Lock()
	defer state.mu.Unlock()
	state.paused = !state.paused
	status := "paused"
	if !state.paused {
		status = "resumed"
	}
	json.NewEncoder(w).Encode(map[string]string{"status": status})
}

func cancelHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	state.mu.Lock()
	defer state.mu.Unlock()
	state.cancelled = true
	json.NewEncoder(w).Encode(map[string]string{"status": "cancelled"})
}

func exportHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	state.mu.Lock()
	results := make([]string, len(state.results))
	copy(results, state.results)
	state.mu.Unlock()

	filename := "hasil_pencarian_" + time.Now().Format("20060102_150405") + ".txt"
	w.Header().Set("Content-Disposition", "attachment; filename="+filename)
	w.Header().Set("Content-Type", "text/plain")
	for _, line := range results {
		fmt.Fprintln(w, line)
	}
}

func statusHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	state.mu.Lock()
	defer state.mu.Unlock()
	json.NewEncoder(w).Encode(map[string]interface{}{
		"running": state.running,
		"paused":  state.paused,
		"count":   len(state.results),
	})
}

func indexHandler(w http.ResponseWriter, r *http.Request) {
	// Serve the HTML file
	http.ServeFile(w, r, filepath.Join(".", "index.html"))
}

func main() {
	port := os.Getenv("PORT")
	if port == "" {
		port = "8181"
	}

	http.HandleFunc("/", indexHandler)
	http.HandleFunc("/search", searchHandler)
	http.HandleFunc("/pause", pauseHandler)
	http.HandleFunc("/cancel", cancelHandler)
	http.HandleFunc("/export", exportHandler)
	http.HandleFunc("/status", statusHandler)

	log.Printf("🚀 Server running at http://localhost:%s", port)
	log.Fatal(http.ListenAndServe(":"+port, nil))
}