package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/rand"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"log"
	"math"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unicode"
)

const (
	defaultDirectory     = `C:\Users\rdp\Desktop\backup\X-LOGS-main\ulp\downloads`
	exactLineThreshold   = 8 << 20
	sampleChunkSize      = 24 << 10
	defaultPageSize      = 100
	maxPageSize          = 500
	maxStoredLineRunes   = 4096
	resultSnippetPadding = 256
	resultEventCountStep = 100
	defaultFilterDir     = "filter"
	randomIDLength       = 5
	engineNative         = "native"
	engineUgrep          = "ugrep"
	engineHybrid         = "hybrid"
	ugrepThreads         = "32"
	maxUgrepBatchFiles   = 256
	maxUgrepBatchBytes   = 16 << 30
	maxUgrepCommandChars = 28000
)

var (
	newlineByte   = []byte{'\n'}
	emailPattern  = regexp.MustCompile(`(?i)[a-z0-9._%+\-]+@[a-z0-9.\-]+\.[a-z]{2,}`)
	domainPattern = regexp.MustCompile(`(?i)(?:https?://)?(?:[a-z0-9](?:[a-z0-9\-]{0,61}[a-z0-9])?\.)+[a-z]{2,63}(?:[/:?#][^\s]*)?`)
)

type SearchState struct {
	mu          sync.Mutex
	pauseCond   *sync.Cond
	paused      atomic.Bool
	cancelled   atomic.Bool
	running     atomic.Bool
	query       string
	engine      string
	fixFilter   bool
	outputDir   string
	filterStats map[string]FilterPanelStat
	results     []string
	cancel      context.CancelFunc
}

func newSearchState() *SearchState {
	state := &SearchState{}
	state.pauseCond = sync.NewCond(&state.mu)
	return state
}

func (s *SearchState) waitIfPaused(ctx context.Context) bool {
	if !s.paused.Load() {
		return ctx.Err() == nil && !s.cancelled.Load()
	}

	s.mu.Lock()
	defer s.mu.Unlock()

	for s.paused.Load() && !s.cancelled.Load() && ctx.Err() == nil {
		s.pauseCond.Wait()
	}

	return ctx.Err() == nil && !s.cancelled.Load()
}

type FileMeta struct {
	Path string
	Size int64
}

type DirectoryStats struct {
	Directory          string     `json:"directory"`
	DirectoryName      string     `json:"directory_name"`
	TotalLogs          int        `json:"total_logs"`
	TotalSizeBytes     int64      `json:"total_size_bytes"`
	TotalSize          string     `json:"total_size"`
	EstimatedLines     int64      `json:"estimated_lines"`
	EstimatedLinesText string     `json:"estimated_lines_text"`
	Files              []FileMeta `json:"-"`
}

type SSEEvent struct {
	Type           string  `json:"type"`
	Data           string  `json:"data,omitempty"`
	Count          int     `json:"count,omitempty"`
	Elapsed        string  `json:"elapsed,omitempty"`
	Progress       float64 `json:"progress"`
	ProcessedBytes int64   `json:"processed_bytes"`
	TotalBytes     int64   `json:"total_bytes"`
	ETA            string  `json:"eta,omitempty"`
	SpeedBytes     float64 `json:"speed_bytes"`
	FilesDone      int     `json:"files_done"`
	TotalFiles     int     `json:"total_files"`
	Engine         string  `json:"engine,omitempty"`
	FixFilter      bool    `json:"fix_filter"`
	OutputDir      string  `json:"output_dir,omitempty"`
}

type ResultsPageResponse struct {
	Items      []string `json:"items"`
	Page       int      `json:"page"`
	PageSize   int      `json:"page_size"`
	TotalCount int      `json:"total_count"`
	TotalPages int      `json:"total_pages"`
}

type SearchBatch struct {
	Files      []FileMeta
	TotalBytes int64
}

type FilterPanelStat struct {
	CMSName    string `json:"cms_name"`
	OutputFile string `json:"output_file"`
	Count      int    `json:"count"`
}

type FilterStatusResponse struct {
	Enabled     bool              `json:"enabled"`
	OutputDir   string            `json:"output_dir"`
	TotalPanels int               `json:"total_panels"`
	TotalLines  int               `json:"total_lines"`
	Query       string            `json:"query"`
	Items       []FilterPanelStat `json:"items"`
}

type CMSRule struct {
	CMSName       string   `json:"cmsName"`
	OutputFile    string   `json:"outputFIle"`
	Pattern       []string `json:"pattern"`
	IsRegex       bool     `json:"isRegex"`
	compiledRegex []*regexp.Regexp
	plainPatterns []string
}

type SearchPipeline struct {
	rules      []CMSRule
	writer     *FilterWriterManager
	outputDir  string
	boundaries []string
}

type FilterWriterManager struct {
	baseDir string
	files   map[string]*searchOutputFile
	seen    map[string]map[string]struct{}
}

type searchOutputFile struct {
	file      *os.File
	writer    *bufio.Writer
	pending   int
	lastFlush time.Time
}

var (
	state          = newSearchState()
	statsOnce      sync.Once
	cachedStats    DirectoryStats
	statsErr       error
	cmsRulesOnce   sync.Once
	cachedCMSRules []CMSRule
	cmsRulesErr    error
)

func enableCORS(w http.ResponseWriter) {
	w.Header().Set("Access-Control-Allow-Origin", "*")
	w.Header().Set("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
	w.Header().Set("Access-Control-Allow-Headers", "Content-Type")
}

func sendSSE(w http.ResponseWriter, event SSEEvent) {
	data, _ := json.Marshal(event)
	fmt.Fprintf(w, "data: %s\n\n", data)
	if f, ok := w.(http.Flusher); ok {
		f.Flush()
	}
}

func getDirectoryStats() (DirectoryStats, error) {
	statsOnce.Do(func() {
		cachedStats, statsErr = buildDirectoryStats(defaultDirectory)
	})
	return cachedStats, statsErr
}

func getCMSRules() ([]CMSRule, error) {
	cmsRulesOnce.Do(func() {
		cachedCMSRules, cmsRulesErr = loadCMSRules(filepath.Join(".", "rules.json"))
	})
	return cachedCMSRules, cmsRulesErr
}

func loadCMSRules(path string) ([]CMSRule, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("failed to read rules file: %w", err)
	}

	var rules []CMSRule
	if err := json.Unmarshal(content, &rules); err != nil {
		return nil, fmt.Errorf("failed to parse rules file: %w", err)
	}

	for i := range rules {
		rules[i].plainPatterns = buildRulePatterns(rules[i].Pattern)
		if !rules[i].IsRegex {
			continue
		}

		for _, pattern := range rules[i].Pattern {
			regexPattern := pattern
			if !strings.HasPrefix(regexPattern, "(?i)") {
				regexPattern = "(?i)" + regexPattern
			}
			compiled, err := regexp.Compile(regexPattern)
			if err != nil {
				log.Printf("skipping invalid regex %q for rule %q: %v", pattern, rules[i].CMSName, err)
				continue
			}
			rules[i].compiledRegex = append(rules[i].compiledRegex, compiled)
		}
	}

	return rules, nil
}

func buildRulePatterns(patterns []string) []string {
	seen := make(map[string]struct{}, len(patterns)*4)
	normalized := make([]string, 0, len(patterns)*4)

	add := func(pattern string) {
		pattern = strings.TrimSpace(strings.ToLower(pattern))
		if pattern == "" {
			return
		}
		if _, ok := seen[pattern]; ok {
			return
		}
		seen[pattern] = struct{}{}
		normalized = append(normalized, pattern)
	}

	for _, pattern := range patterns {
		lower := strings.ToLower(pattern)
		add(lower)
		add(strings.ReplaceAll(lower, ":", "|"))
		add(strings.ReplaceAll(lower, " ", ""))
		add(strings.ReplaceAll(strings.ReplaceAll(lower, ":", "|"), " ", ""))
	}

	return normalized
}

func newSearchPipeline(query string, rules []CMSRule) (*SearchPipeline, error) {
	randomID, err := randomString(randomIDLength)
	if err != nil {
		return nil, err
	}

	outputDir := filepath.Join(defaultFilterDir, sanitizeFilename(query)+"-"+randomID)
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		return nil, fmt.Errorf("failed to create filter output directory: %w", err)
	}

	return &SearchPipeline{
		rules:      rules,
		writer:     newFilterWriterManager(outputDir),
		outputDir:  outputDir,
		boundaries: buildRuleBoundaries(rules),
	}, nil
}

func (p *SearchPipeline) Process(line string) (string, *CMSRule, bool, error) {
	if p == nil {
		return line, nil, true, nil
	}

	fixed := fixSearchResultLine(line, p.boundaries)
	if fixed == "" {
		return "", nil, false, nil
	}

	rule := matchCMSRule(p.rules, fixed)
	if rule == nil {
		return "", nil, false, nil
	}

	wrote, err := p.writer.Write(rule.OutputFile, fixed)
	if err != nil {
		return "", nil, false, err
	}
	if !wrote {
		return "", nil, false, nil
	}

	return fixed, rule, true, nil
}

func (p *SearchPipeline) Close() error {
	if p == nil || p.writer == nil {
		return nil
	}
	return p.writer.Close()
}

func newFilterWriterManager(baseDir string) *FilterWriterManager {
	return &FilterWriterManager{
		baseDir: baseDir,
		files:   make(map[string]*searchOutputFile),
		seen:    make(map[string]map[string]struct{}),
	}
}

func (m *FilterWriterManager) Write(relativePath, line string) (bool, error) {
	cleanRelativePath, err := sanitizeRelativeOutputPath(relativePath)
	if err != nil {
		return false, err
	}

	fullPath := filepath.Join(m.baseDir, cleanRelativePath)
	seenForFile := m.seen[fullPath]
	if seenForFile == nil {
		seenForFile = make(map[string]struct{})
		m.seen[fullPath] = seenForFile
	}
	if _, exists := seenForFile[line]; exists {
		return false, nil
	}
	seenForFile[line] = struct{}{}

	if err := os.MkdirAll(filepath.Dir(fullPath), 0o755); err != nil {
		return false, fmt.Errorf("failed to prepare output directory: %w", err)
	}

	handle := m.files[fullPath]
	if handle == nil {
		file, err := os.OpenFile(fullPath, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0o644)
		if err != nil {
			return false, fmt.Errorf("failed to open output file %s: %w", fullPath, err)
		}
		handle = &searchOutputFile{
			file:      file,
			writer:    bufio.NewWriterSize(file, 1<<20),
			lastFlush: time.Now(),
		}
		m.files[fullPath] = handle
	}

	if _, err := handle.writer.WriteString(line + "\n"); err != nil {
		return false, fmt.Errorf("failed to write output file %s: %w", fullPath, err)
	}

	handle.pending++
	if handle.pending >= 128 || time.Since(handle.lastFlush) >= time.Second {
		if err := handle.writer.Flush(); err != nil {
			return false, fmt.Errorf("failed to flush output file %s: %w", fullPath, err)
		}
		handle.pending = 0
		handle.lastFlush = time.Now()
	}

	return true, nil
}

func (m *FilterWriterManager) Close() error {
	if m == nil {
		return nil
	}

	var closeErr error
	for path, handle := range m.files {
		if handle.writer != nil {
			if err := handle.writer.Flush(); err != nil && closeErr == nil {
				closeErr = fmt.Errorf("failed to flush output file %s: %w", path, err)
			}
		}
		if handle.file != nil {
			if err := handle.file.Close(); err != nil && closeErr == nil {
				closeErr = fmt.Errorf("failed to close output file %s: %w", path, err)
			}
		}
	}
	return closeErr
}

func buildDirectoryStats(directory string) (DirectoryStats, error) {
	files := make([]FileMeta, 0, 1024)
	var totalSize int64

	err := filepath.WalkDir(directory, func(path string, d fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return nil
		}
		if d.IsDir() {
			return nil
		}
		if !strings.EqualFold(filepath.Ext(d.Name()), ".txt") {
			return nil
		}

		info, err := d.Info()
		if err != nil {
			return nil
		}

		size := info.Size()
		totalSize += size
		files = append(files, FileMeta{
			Path: path,
			Size: size,
		})
		return nil
	})
	if err != nil {
		return DirectoryStats{}, err
	}

	estimatedLines := estimateDirectoryLines(files)

	return DirectoryStats{
		Directory:          directory,
		DirectoryName:      baseName(directory),
		TotalLogs:          len(files),
		TotalSizeBytes:     totalSize,
		TotalSize:          formatSize(totalSize),
		EstimatedLines:     estimatedLines,
		EstimatedLinesText: formatLineEstimate(estimatedLines),
		Files:              files,
	}, nil
}

func estimateDirectoryLines(files []FileMeta) int64 {
	if len(files) == 0 {
		return 0
	}

	workerCount := minInt(runtime.NumCPU(), len(files))
	if workerCount < 1 {
		workerCount = 1
	}

	fileCh := make(chan FileMeta, workerCount*2)
	var totalLines int64
	var wg sync.WaitGroup

	for i := 0; i < workerCount; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for file := range fileCh {
				estimated, err := estimateLineCount(file)
				if err != nil {
					continue
				}
				atomic.AddInt64(&totalLines, estimated)
			}
		}()
	}

	for _, file := range files {
		fileCh <- file
	}
	close(fileCh)
	wg.Wait()

	return totalLines
}

func estimateLineCount(file FileMeta) (int64, error) {
	if file.Size == 0 {
		return 0, nil
	}
	if file.Size <= exactLineThreshold {
		return exactLineCount(file.Path)
	}

	f, err := os.Open(file.Path)
	if err != nil {
		return 0, err
	}
	defer f.Close()

	var sampleBytes int64
	var sampleLines int64

	for _, offset := range sampleOffsets(file.Size) {
		size := minInt64(sampleChunkSize, file.Size-offset)
		if size <= 0 {
			continue
		}

		buf := make([]byte, size)
		n, err := f.ReadAt(buf, offset)
		if err != nil && err != io.EOF {
			return 0, err
		}
		if n == 0 {
			continue
		}

		sampleBytes += int64(n)
		sampleLines += int64(bytes.Count(buf[:n], newlineByte))
	}

	if sampleLines == 0 {
		if file.Size <= 64<<20 {
			return exactLineCount(file.Path)
		}
		return int64(math.Max(1, math.Round(float64(file.Size)/120))), nil
	}

	bytesPerLine := float64(sampleBytes) / float64(sampleLines)
	estimate := int64(math.Round(float64(file.Size) / bytesPerLine))
	if estimate < 1 {
		estimate = 1
	}
	return estimate, nil
}

func exactLineCount(path string) (int64, error) {
	f, err := os.Open(path)
	if err != nil {
		return 0, err
	}
	defer f.Close()

	reader := bufio.NewReaderSize(f, 1<<20)
	buf := make([]byte, 1<<20)

	var total int64
	var lastByte byte
	var readAny bool

	for {
		n, err := reader.Read(buf)
		if n > 0 {
			readAny = true
			lastByte = buf[n-1]
			total += int64(bytes.Count(buf[:n], newlineByte))
		}
		if err == io.EOF {
			break
		}
		if err != nil {
			return 0, err
		}
	}

	if readAny && lastByte != '\n' {
		total++
	}

	return total, nil
}

func searchHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	query := strings.TrimSpace(r.URL.Query().Get("query"))
	if query == "" {
		http.Error(w, "query required", http.StatusBadRequest)
		return
	}
	engine := normalizeEngine(r.URL.Query().Get("engine"))
	if engine == "" {
		http.Error(w, "invalid engine", http.StatusBadRequest)
		return
	}
	fixFilterEnabled := parseFeatureToggle(r.URL.Query().Get("fix_filter"))

	w.Header().Set("Content-Type", "text/event-stream")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("X-Accel-Buffering", "no")
	enableCORS(w)

	if engine != engineNative {
		if _, err := exec.LookPath("ugrep"); err != nil {
			sendSSE(w, SSEEvent{Type: "error", Data: "ugrep binary not found on server"})
			return
		}
	}

	var pipeline *SearchPipeline
	outputDir := ""
	if fixFilterEnabled {
		rules, err := getCMSRules()
		if err != nil {
			sendSSE(w, SSEEvent{Type: "error", Data: err.Error()})
			return
		}

		pipeline, err = newSearchPipeline(query, rules)
		if err != nil {
			sendSSE(w, SSEEvent{Type: "error", Data: err.Error()})
			return
		}
		outputDir = pipeline.outputDir
		defer func() {
			if err := pipeline.Close(); err != nil {
				log.Printf("failed to finalize filter output: %v", err)
			}
		}()
	}

	stats, err := getDirectoryStats()
	if err != nil {
		sendSSE(w, SSEEvent{Type: "error", Data: err.Error()})
		return
	}

	state.mu.Lock()
	if state.running.Load() {
		state.mu.Unlock()
		sendSSE(w, SSEEvent{Type: "error", Data: "search already running"})
		return
	}

	ctx, cancel := context.WithCancel(r.Context())
	state.running.Store(true)
	state.paused.Store(false)
	state.cancelled.Store(false)
	state.query = query
	state.engine = engine
	state.fixFilter = fixFilterEnabled
	state.outputDir = outputDir
	state.filterStats = make(map[string]FilterPanelStat)
	state.results = state.results[:0]
	state.cancel = cancel
	state.mu.Unlock()

	go func() {
		<-ctx.Done()
		state.mu.Lock()
		state.pauseCond.Broadcast()
		state.mu.Unlock()
	}()

	defer func() {
		cancel()
		state.mu.Lock()
		state.cancel = nil
		state.paused.Store(false)
		state.running.Store(false)
		state.pauseCond.Broadcast()
		state.mu.Unlock()
	}()

	startTime := time.Now()
	sendSSE(w, SSEEvent{
		Type:       "start",
		Data:       fmt.Sprintf("[%s] searching for %q", engine, query),
		TotalBytes: stats.TotalSizeBytes,
		TotalFiles: stats.TotalLogs,
		Engine:     engine,
		FixFilter:  fixFilterEnabled,
		OutputDir:  outputDir,
	})

	if stats.TotalLogs == 0 {
		sendSSE(w, buildProgressEvent("done", "no .txt files found", startTime, 0, 0, 0, 0, 0))
		return
	}

	resultCh := make(chan string, 256)
	errCh := make(chan error, 1)

	var processedBytes int64
	var filesDone int64
	lowerQuery := strings.ToLower(query)
	startSearchEngine(ctx, engine, query, lowerQuery, stats.Files, resultCh, errCh, &processedBytes, &filesDone)

	progressTicker := time.NewTicker(300 * time.Millisecond)
	defer progressTicker.Stop()

	matchCount := 0
	lastResultCount := 0
	lastResultEventAt := time.Now()

	for resultCh != nil {
		select {
		case err := <-errCh:
			sendSSE(w, SSEEvent{Type: "error", Data: err.Error()})
			return
		case line, ok := <-resultCh:
			if !ok {
				resultCh = nil
				continue
			}

			if pipeline != nil {
				processedLine, matchedRule, keep, err := pipeline.Process(line)
				if err != nil {
					sendSSE(w, SSEEvent{Type: "error", Data: err.Error()})
					return
				}
				if !keep {
					continue
				}
				line = processedLine
				if matchedRule != nil {
					state.mu.Lock()
					stat := state.filterStats[matchedRule.OutputFile]
					stat.CMSName = matchedRule.CMSName
					stat.OutputFile = matchedRule.OutputFile
					stat.Count++
					state.filterStats[matchedRule.OutputFile] = stat
					state.mu.Unlock()
				}
			}

			matchCount++
			state.mu.Lock()
			state.results = append(state.results, line)
			state.mu.Unlock()

			if matchCount == 1 || matchCount-lastResultCount >= resultEventCountStep || time.Since(lastResultEventAt) >= 150*time.Millisecond {
				sendSSE(w, SSEEvent{
					Type:    "result",
					Count:   matchCount,
					Elapsed: time.Since(startTime).Round(time.Millisecond).String(),
				})
				lastResultCount = matchCount
				lastResultEventAt = time.Now()
			}

		case <-progressTicker.C:
			sendSSE(w, buildProgressEvent(
				"progress",
				"",
				startTime,
				matchCount,
				atomic.LoadInt64(&processedBytes),
				stats.TotalSizeBytes,
				int(atomic.LoadInt64(&filesDone)),
				stats.TotalLogs,
			))
		}
	}

	if state.cancelled.Load() || ctx.Err() != nil {
		sendSSE(w, buildProgressEvent(
			"cancelled",
			"search cancelled",
			startTime,
			matchCount,
			atomic.LoadInt64(&processedBytes),
			stats.TotalSizeBytes,
			int(atomic.LoadInt64(&filesDone)),
			stats.TotalLogs,
		))
		return
	}

	sendSSE(w, buildProgressEvent(
		"done",
		"search complete",
		startTime,
		matchCount,
		stats.TotalSizeBytes,
		stats.TotalSizeBytes,
		stats.TotalLogs,
		stats.TotalLogs,
	))
}

func startSearchEngine(ctx context.Context, engine, query, lowerQuery string, files []FileMeta, resultCh chan string, errCh chan error, processedBytes *int64, filesDone *int64) {
	switch engine {
	case engineNative:
		startNativeWorkers(ctx, lowerQuery, files, resultCh, processedBytes, filesDone)
	case engineUgrep:
		go runUgrepBatches(ctx, query, lowerQuery, files, resultCh, errCh, processedBytes, filesDone, false)
	case engineHybrid:
		go runUgrepBatches(ctx, query, lowerQuery, files, resultCh, errCh, processedBytes, filesDone, true)
	default:
		go func() {
			defer close(resultCh)
			select {
			case errCh <- fmt.Errorf("unsupported engine: %s", engine):
			default:
			}
		}()
	}
}

func startNativeWorkers(ctx context.Context, lowerQuery string, files []FileMeta, resultCh chan string, processedBytes *int64, filesDone *int64) {
	fileCh := make(chan FileMeta, minInt(len(files), maxInt(2, runtime.NumCPU()*2)))
	var wg sync.WaitGroup

	workerCount := minInt(runtime.NumCPU(), len(files))
	if workerCount < 1 {
		workerCount = 1
	}

	for i := 0; i < workerCount; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			searchWorker(ctx, lowerQuery, fileCh, resultCh, processedBytes, filesDone)
		}()
	}

	go func() {
		defer close(fileCh)
		for _, file := range files {
			select {
			case <-ctx.Done():
				return
			case fileCh <- file:
			}
		}
	}()

	go func() {
		wg.Wait()
		close(resultCh)
	}()
}

func runUgrepBatches(ctx context.Context, query, lowerQuery string, files []FileMeta, resultCh chan string, errCh chan error, processedBytes *int64, filesDone *int64, hybrid bool) {
	defer close(resultCh)

	batches := buildUgrepBatches(files)
	for _, batch := range batches {
		if ctx.Err() != nil || state.cancelled.Load() {
			return
		}
		if !state.waitIfPaused(ctx) {
			return
		}
		if err := runUgrepBatch(ctx, query, lowerQuery, batch, resultCh, hybrid); err != nil {
			select {
			case errCh <- err:
			default:
			}
			return
		}
		atomic.AddInt64(processedBytes, batch.TotalBytes)
		atomic.AddInt64(filesDone, int64(len(batch.Files)))
	}
}

func buildUgrepBatches(files []FileMeta) []SearchBatch {
	batches := make([]SearchBatch, 0, 64)
	current := SearchBatch{
		Files: make([]FileMeta, 0, maxUgrepBatchFiles),
	}
	currentChars := 128

	flush := func() {
		if len(current.Files) == 0 {
			return
		}
		batches = append(batches, current)
		current = SearchBatch{
			Files: make([]FileMeta, 0, maxUgrepBatchFiles),
		}
		currentChars = 128
	}

	for _, file := range files {
		nextChars := currentChars + len(file.Path) + 1
		if len(current.Files) > 0 && (len(current.Files) >= maxUgrepBatchFiles || current.TotalBytes+file.Size > maxUgrepBatchBytes || nextChars > maxUgrepCommandChars) {
			flush()
		}

		current.Files = append(current.Files, file)
		current.TotalBytes += file.Size
		currentChars += len(file.Path) + 1
	}

	flush()
	return batches
}

func runUgrepBatch(ctx context.Context, query, lowerQuery string, batch SearchBatch, resultCh chan<- string, hybrid bool) error {
	args := []string{
		"-F",
		"-i",
		"-I",
		"-J", ugrepThreads,
		"--no-filename",
		"--no-messages",
		query,
	}
	for _, file := range batch.Files {
		args = append(args, file.Path)
	}

	cmd := exec.CommandContext(ctx, "ugrep", args...)
	cmd.Stderr = io.Discard
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return fmt.Errorf("failed to open ugrep stdout: %w", err)
	}

	if err := cmd.Start(); err != nil {
		return fmt.Errorf("failed to start ugrep (engine=%s): %w", engineUgrep, err)
	}

	reader := bufio.NewReaderSize(stdout, 1<<20)
	for {
		rawLine, readErr := reader.ReadBytes('\n')
		if len(rawLine) > 0 {
			if ctx.Err() != nil || state.cancelled.Load() {
				_ = cmd.Wait()
				return nil
			}
			if !state.waitIfPaused(ctx) {
				_ = cmd.Wait()
				return nil
			}

			line := strings.TrimRight(strings.ToValidUTF8(string(rawLine), " "), "\r\n")
			var output string
			if hybrid {
				normalized, ok := normalizeMatchedLine([]byte(line), lowerQuery)
				if !ok {
					goto nextLine
				}
				output = normalized
			} else {
				output = sanitizeDisplayLine(line)
				if output == "" {
					goto nextLine
				}
			}

			select {
			case <-ctx.Done():
				_ = cmd.Wait()
				return nil
			case resultCh <- output:
			}
		}
	nextLine:
		if readErr == io.EOF {
			break
		}
		if readErr != nil {
			_ = cmd.Wait()
			return fmt.Errorf("ugrep read failed: %w", readErr)
		}
	}

	if err := cmd.Wait(); err != nil && ctx.Err() == nil && !state.cancelled.Load() && !isExpectedUgrepExit(err) {
		return fmt.Errorf("ugrep wait failed: %w", err)
	}

	return nil
}

func searchWorker(ctx context.Context, lowerQuery string, fileCh <-chan FileMeta, resultCh chan<- string, processedBytes *int64, filesDone *int64) {
	for {
		select {
		case <-ctx.Done():
			return
		case file, ok := <-fileCh:
			if !ok {
				return
			}

			if !state.waitIfPaused(ctx) {
				return
			}
			if searchFile(ctx, lowerQuery, file, resultCh, processedBytes) {
				atomic.AddInt64(filesDone, 1)
			}
		}
	}
}

func searchFile(ctx context.Context, lowerQuery string, file FileMeta, resultCh chan<- string, processedBytes *int64) bool {
	f, err := os.Open(file.Path)
	if err != nil {
		atomic.AddInt64(processedBytes, file.Size)
		return true
	}
	defer f.Close()

	reader := bufio.NewReaderSize(f, 1<<20)
	var bytesRead int64

	for {
		if state.cancelled.Load() || ctx.Err() != nil {
			return false
		}
		if !state.waitIfPaused(ctx) {
			return false
		}

		rawLine, err := reader.ReadBytes('\n')
		if len(rawLine) > 0 {
			bytesRead += int64(len(rawLine))
			atomic.AddInt64(processedBytes, int64(len(rawLine)))

			line, ok := normalizeMatchedLine(rawLine, lowerQuery)
			if ok {
				select {
				case <-ctx.Done():
					return false
				case resultCh <- line:
				}
			}
		}

		if err == io.EOF {
			if bytesRead < file.Size {
				atomic.AddInt64(processedBytes, file.Size-bytesRead)
			}
			return true
		}
		if err != nil {
			if bytesRead < file.Size {
				atomic.AddInt64(processedBytes, file.Size-bytesRead)
			}
			return true
		}
	}
}

func normalizeMatchedLine(rawLine []byte, lowerQuery string) (string, bool) {
	line := strings.TrimRight(strings.ToValidUTF8(string(rawLine), " "), "\r\n")
	if line == "" {
		return "", false
	}

	var builder strings.Builder
	builder.Grow(minInt(len(line), maxStoredLineRunes))

	lastWasSpace := false
	for _, r := range line {
		switch {
		case r == '\r' || r == '\n' || r == '\t':
			if !lastWasSpace && builder.Len() > 0 {
				builder.WriteByte(' ')
				lastWasSpace = true
			}
		case unicode.IsSpace(r):
			if !lastWasSpace && builder.Len() > 0 {
				builder.WriteByte(' ')
				lastWasSpace = true
			}
		case !unicode.IsGraphic(r):
			if !lastWasSpace && builder.Len() > 0 {
				builder.WriteByte(' ')
				lastWasSpace = true
			}
		default:
			builder.WriteRune(r)
			lastWasSpace = false
		}
	}

	normalized := strings.TrimSpace(builder.String())
	if normalized == "" {
		return "", false
	}
	if !strings.Contains(strings.ToLower(normalized), lowerQuery) {
		return "", false
	}
	if !containsRelevantToken(normalized) {
		return "", false
	}

	normalized = extractRelevantSegment(normalized)
	if normalized == "" {
		return "", false
	}
	if !strings.Contains(strings.ToLower(normalized), lowerQuery) {
		return "", false
	}

	if len([]rune(normalized)) > maxStoredLineRunes {
		normalized = shrinkResultLine(normalized, lowerQuery)
	}

	return normalized, true
}

func sanitizeDisplayLine(rawLine string) string {
	line := strings.TrimRight(strings.ToValidUTF8(rawLine, " "), "\r\n")
	if line == "" {
		return ""
	}

	var builder strings.Builder
	builder.Grow(minInt(len(line), maxStoredLineRunes))

	lastWasSpace := false
	for _, r := range line {
		switch {
		case r == '\r' || r == '\n' || r == '\t':
			if !lastWasSpace && builder.Len() > 0 {
				builder.WriteByte(' ')
				lastWasSpace = true
			}
		case unicode.IsSpace(r):
			if !lastWasSpace && builder.Len() > 0 {
				builder.WriteByte(' ')
				lastWasSpace = true
			}
		case !unicode.IsGraphic(r):
			if !lastWasSpace && builder.Len() > 0 {
				builder.WriteByte(' ')
				lastWasSpace = true
			}
		default:
			builder.WriteRune(r)
			lastWasSpace = false
		}
	}

	cleaned := strings.TrimSpace(builder.String())
	if cleaned == "" || !containsRelevantToken(cleaned) {
		return ""
	}

	cleaned = extractRelevantSegment(cleaned)
	if cleaned == "" {
		return ""
	}
	if len([]rune(cleaned)) > maxStoredLineRunes {
		cleaned = shrinkResultLine(cleaned, "")
	}

	return cleaned
}

func containsRelevantToken(line string) bool {
	return emailPattern.MatchString(line) || domainPattern.MatchString(line)
}

func extractRelevantSegment(line string) string {
	emailIdx := emailPattern.FindStringIndex(line)
	domainIdx := domainPattern.FindStringIndex(line)

	start := -1
	switch {
	case emailIdx != nil && domainIdx != nil:
		start = minInt(emailIdx[0], domainIdx[0])
	case emailIdx != nil:
		start = emailIdx[0]
	case domainIdx != nil:
		start = domainIdx[0]
	}

	if start <= 0 {
		return strings.TrimSpace(line)
	}

	segment := strings.TrimSpace(line[start:])
	segment = strings.TrimLeft(segment, " |:-")
	return strings.TrimSpace(segment)
}

func shrinkResultLine(line, lowerQuery string) string {
	runes := []rune(line)
	if len(runes) <= maxStoredLineRunes {
		return line
	}

	focus := 0
	if lowerQuery != "" {
		focus = strings.Index(strings.ToLower(line), lowerQuery)
		if focus < 0 {
			focus = 0
		} else {
			focus = len([]rune(line[:focus]))
		}
	}

	start := maxInt(0, focus-resultSnippetPadding)
	end := minInt(len(runes), start+maxStoredLineRunes)
	if end-start < maxStoredLineRunes {
		start = maxInt(0, end-maxStoredLineRunes)
	}

	snippet := string(runes[start:end])
	if start > 0 {
		snippet = "..." + strings.TrimLeft(snippet, " ")
	}
	if end < len(runes) {
		snippet = strings.TrimRight(snippet, " ") + "..."
	}
	return snippet
}

func buildProgressEvent(kind, data string, startTime time.Time, count int, processedBytes, totalBytes int64, filesDone, totalFiles int) SSEEvent {
	if totalBytes > 0 && processedBytes > totalBytes {
		processedBytes = totalBytes
	}

	progress := 0.0
	if totalBytes > 0 {
		progress = (float64(processedBytes) / float64(totalBytes)) * 100
	}

	elapsed := time.Since(startTime)
	speedBytes := 0.0
	if elapsed > 0 {
		speedBytes = float64(processedBytes) / elapsed.Seconds()
	}

	eta := "--"
	switch kind {
	case "done":
		progress = 100
		eta = "0s"
	case "cancelled":
		eta = "stopped"
	default:
		if totalBytes > processedBytes && speedBytes > 0 {
			remaining := float64(totalBytes - processedBytes)
			eta = formatETA(time.Duration((remaining / speedBytes) * float64(time.Second)))
		}
	}

	return SSEEvent{
		Type:           kind,
		Data:           data,
		Count:          count,
		Elapsed:        elapsed.Round(time.Millisecond).String(),
		Progress:       progress,
		ProcessedBytes: processedBytes,
		TotalBytes:     totalBytes,
		ETA:            eta,
		SpeedBytes:     speedBytes,
		FilesDone:      filesDone,
		TotalFiles:     totalFiles,
	}
}

func pauseHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	if !state.running.Load() {
		json.NewEncoder(w).Encode(map[string]string{"status": "idle"})
		return
	}

	state.mu.Lock()
	paused := !state.paused.Load()
	state.paused.Store(paused)
	if !paused {
		state.pauseCond.Broadcast()
	}
	state.mu.Unlock()

	status := "paused"
	if !paused {
		status = "resumed"
	}

	json.NewEncoder(w).Encode(map[string]string{"status": status})
}

func cancelHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	state.mu.Lock()
	state.cancelled.Store(true)
	cancel := state.cancel
	state.pauseCond.Broadcast()
	state.mu.Unlock()

	if cancel != nil {
		cancel()
	}

	json.NewEncoder(w).Encode(map[string]string{"status": "cancelled"})
}

func exportHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	state.mu.Lock()
	results := make([]string, len(state.results))
	query := state.query
	copy(results, state.results)
	state.mu.Unlock()

	filename := sanitizeFilename(query) + "_" + time.Now().Format("20060102_150405") + ".txt"
	w.Header().Set("Content-Disposition", "attachment; filename="+filename)
	w.Header().Set("Content-Type", "text/plain")
	for _, line := range results {
		fmt.Fprintln(w, line)
	}
}

func resultsHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	page, pageSize := parsePageParams(r)

	state.mu.Lock()
	totalCount := len(state.results)
	totalPages := maxInt(1, (totalCount+pageSize-1)/pageSize)
	if page > totalPages {
		page = totalPages
	}

	start := (page - 1) * pageSize
	if start > totalCount {
		start = totalCount
	}
	end := minInt(start+pageSize, totalCount)
	items := make([]string, end-start)
	copy(items, state.results[start:end])
	state.mu.Unlock()

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(ResultsPageResponse{
		Items:      items,
		Page:       page,
		PageSize:   pageSize,
		TotalCount: totalCount,
		TotalPages: totalPages,
	})
}

func statsHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	stats, err := getDirectoryStats()
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(stats)
}

func statusHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	state.mu.Lock()
	count := len(state.results)
	engine := state.engine
	fixFilter := state.fixFilter
	outputDir := state.outputDir
	state.mu.Unlock()

	json.NewEncoder(w).Encode(map[string]interface{}{
		"running":    state.running.Load(),
		"paused":     state.paused.Load(),
		"cancelled":  state.cancelled.Load(),
		"count":      count,
		"directory":  defaultDirectory,
		"engine":     engine,
		"fix_filter": fixFilter,
		"output_dir": outputDir,
	})
}

func filterStatusHandler(w http.ResponseWriter, r *http.Request) {
	enableCORS(w)
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return
	}

	state.mu.Lock()
	enabled := state.fixFilter
	outputDir := state.outputDir
	query := state.query
	items := make([]FilterPanelStat, 0, len(state.filterStats))
	totalLines := 0
	for _, stat := range state.filterStats {
		items = append(items, stat)
		totalLines += stat.Count
	}
	state.mu.Unlock()

	sort.Slice(items, func(i, j int) bool {
		if items[i].Count == items[j].Count {
			if items[i].CMSName == items[j].CMSName {
				return items[i].OutputFile < items[j].OutputFile
			}
			return items[i].CMSName < items[j].CMSName
		}
		return items[i].Count > items[j].Count
	})

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(FilterStatusResponse{
		Enabled:     enabled,
		OutputDir:   outputDir,
		TotalPanels: len(items),
		TotalLines:  totalLines,
		Query:       query,
		Items:       items,
	})
}

func parsePageParams(r *http.Request) (int, int) {
	page := 1
	pageSize := defaultPageSize

	if raw := r.URL.Query().Get("page"); raw != "" {
		if value, err := strconv.Atoi(raw); err == nil && value > 0 {
			page = value
		}
	}
	if raw := r.URL.Query().Get("page_size"); raw != "" {
		if value, err := strconv.Atoi(raw); err == nil && value > 0 {
			pageSize = minInt(value, maxPageSize)
		}
	}

	return page, pageSize
}

func normalizeEngine(raw string) string {
	switch strings.ToLower(strings.TrimSpace(raw)) {
	case "", engineNative:
		return engineNative
	case engineUgrep:
		return engineUgrep
	case engineHybrid:
		return engineHybrid
	default:
		return ""
	}
}

func parseFeatureToggle(raw string) bool {
	switch strings.ToLower(strings.TrimSpace(raw)) {
	case "", "1", "true", "yes", "on", "enable", "enabled":
		return true
	case "0", "false", "no", "off", "disable", "disabled":
		return false
	default:
		return true
	}
}

func sanitizeFilename(input string) string {
	input = strings.TrimSpace(input)
	if input == "" {
		return "results"
	}

	var builder strings.Builder
	lastUnderscore := false

	for _, r := range input {
		switch {
		case unicode.IsLetter(r) || unicode.IsDigit(r):
			builder.WriteRune(unicode.ToLower(r))
			lastUnderscore = false
		case r == '.' || r == '-' || r == '_':
			builder.WriteRune(r)
			lastUnderscore = false
		default:
			if !lastUnderscore && builder.Len() > 0 {
				builder.WriteByte('_')
				lastUnderscore = true
			}
		}
	}

	name := strings.Trim(builder.String(), "._-")
	if name == "" {
		return "results"
	}

	return name
}

func sanitizeRelativeOutputPath(input string) (string, error) {
	cleaned := filepath.Clean(strings.TrimSpace(input))
	cleaned = strings.TrimLeft(cleaned, `/\`)
	switch {
	case cleaned == "", cleaned == ".", strings.HasPrefix(cleaned, ".."):
		return "", fmt.Errorf("invalid output path: %q", input)
	default:
		return cleaned, nil
	}
}

func buildRuleBoundaries(rules []CMSRule) []string {
	seen := make(map[string]struct{}, len(rules)*4)
	boundaries := make([]string, 0, len(rules)*4+24)

	add := func(value string) {
		value = strings.ToLower(strings.TrimSpace(value))
		value = strings.TrimRight(value, "/")
		if value == "" {
			return
		}
		if _, exists := seen[value]; exists {
			return
		}
		seen[value] = struct{}{}
		boundaries = append(boundaries, value)
	}

	common := []string{
		"/auth/login",
		"/auth/signin",
		"/auth/sign-in",
		"/login",
		"/signin",
		"/sign-in",
		"/sign_in",
		"/logon",
		"/user/login",
		"/users/login",
		"/member/login",
		"/account/login",
		"/portal/login",
		"/panel/login",
		"/admin/login",
		"/administrator/login",
		"/wp-login.php",
		"/administrator/index.php",
		"/administrator",
		"/admin",
	}
	for _, boundary := range common {
		add(boundary)
	}

	for _, rule := range rules {
		for _, pattern := range rule.Pattern {
			candidate := strings.ToLower(strings.TrimSpace(pattern))
			candidate = strings.ReplaceAll(candidate, " ", "")
			if candidate == "" || strings.ContainsAny(candidate, "|:") {
				continue
			}

			if strings.HasPrefix(candidate, "/") {
				add(candidate)
				continue
			}

			if idx := strings.Index(candidate, "/"); idx > 0 && idx < len(candidate)-1 {
				add(candidate[idx:])
			}
		}
	}

	sort.Slice(boundaries, func(i, j int) bool {
		if len(boundaries[i]) == len(boundaries[j]) {
			return boundaries[i] < boundaries[j]
		}
		return len(boundaries[i]) > len(boundaries[j])
	})

	return boundaries
}

func fixSearchResultLine(line string, boundaries []string) string {
	cleaned := normalizeFixedSearchLine(line)
	if cleaned == "" {
		return ""
	}

	left, password, ok := splitTrailingCredential(cleaned)
	if !ok {
		return cleaned
	}

	password = cleanCredentialToken(password)
	if !isLikelyPasswordToken(password) {
		return cleaned
	}

	urlPart, userPart, ok := splitURLAndUser(left, boundaries)
	if !ok {
		return cleaned
	}

	urlPart = normalizeURLCandidate(urlPart)
	userPart = cleanCredentialToken(userPart)
	if urlPart == "" || !isLikelyUserToken(userPart) {
		return cleaned
	}

	return urlPart + "|" + userPart + "|" + password
}

func normalizeFixedSearchLine(line string) string {
	cleaned := strings.TrimSpace(strings.ToValidUTF8(line, ""))
	if cleaned == "" {
		return ""
	}

	cleaned = extractRelevantSegment(cleaned)
	cleaned = strings.NewReplacer(
		"\r", "",
		"\n", "",
		"\t", "",
		" ", "",
		";", "|",
	).Replace(cleaned)
	if cleaned == "" {
		return ""
	}

	return normalizeURLCandidate(cleaned)
}

func splitTrailingCredential(line string) (string, string, bool) {
	index := findLastCredentialSeparator(line, len(line))
	if index <= 0 || index >= len(line)-1 {
		return "", "", false
	}
	return line[:index], line[index+1:], true
}

func splitURLAndUser(left string, boundaries []string) (string, string, bool) {
	if urlPart, userPart, ok := splitWithExplicitUserSeparator(left); ok {
		return urlPart, userPart, true
	}
	if urlPart, userPart, ok := splitWithBoundary(left, boundaries); ok {
		return urlPart, userPart, true
	}
	if urlPart, userPart, ok := splitWithTrailingEmail(left); ok {
		return urlPart, userPart, true
	}
	if urlPart, userPart, ok := splitWithTrailingSlash(left); ok {
		return urlPart, userPart, true
	}
	return "", "", false
}

func splitWithExplicitUserSeparator(left string) (string, string, bool) {
	index := findLastCredentialSeparator(left, len(left))
	if index <= 0 || index >= len(left)-1 {
		return "", "", false
	}

	userPart := cleanCredentialToken(left[index+1:])
	if !isLikelyUserToken(userPart) {
		return "", "", false
	}

	urlPart := left[:index]
	if normalizeURLCandidate(urlPart) == "" {
		return "", "", false
	}

	return urlPart, userPart, true
}

func splitWithTrailingEmail(left string) (string, string, bool) {
	matches := emailPattern.FindAllStringIndex(left, -1)
	for i := len(matches) - 1; i >= 0; i-- {
		start, end := matches[i][0], matches[i][1]
		if end != len(left) {
			continue
		}

		userPart := cleanCredentialToken(left[start:end])
		urlPart := trimJoinedURL(left[:start])
		if normalizeURLCandidate(urlPart) == "" || !isLikelyUserToken(userPart) {
			continue
		}

		return urlPart, userPart, true
	}
	return "", "", false
}

func splitWithBoundary(left string, boundaries []string) (string, string, bool) {
	lowerLeft := strings.ToLower(left)
	bestEnd := -1
	bestLength := -1
	bestURL := ""
	bestUser := ""

	for _, boundary := range boundaries {
		index := strings.LastIndex(lowerLeft, boundary)
		if index < 0 {
			continue
		}

		end := index + len(boundary)
		if end >= len(left) {
			continue
		}

		urlPart := left[:end]
		userPart := cleanCredentialToken(left[end:])
		if !isLikelyUserToken(userPart) && end < len(left) && left[end] == '/' {
			userPart = cleanCredentialToken(left[end+1:])
		}
		if !isLikelyUserToken(userPart) {
			continue
		}

		urlPart = trimJoinedURL(urlPart)
		if normalizeURLCandidate(urlPart) == "" {
			continue
		}

		if end > bestEnd || (end == bestEnd && len(boundary) > bestLength) {
			bestEnd = end
			bestLength = len(boundary)
			bestURL = urlPart
			bestUser = userPart
		}
	}

	if bestEnd < 0 {
		return "", "", false
	}
	return bestURL, bestUser, true
}

func splitWithTrailingSlash(left string) (string, string, bool) {
	index := strings.LastIndex(left, "/")
	schemeIndex := strings.Index(left, "://")
	if index <= 0 || index >= len(left)-1 || (schemeIndex >= 0 && index <= schemeIndex+2) {
		return "", "", false
	}

	userPart := cleanCredentialToken(left[index+1:])
	if !isLikelyUserToken(userPart) {
		return "", "", false
	}

	urlPart := trimJoinedURL(left[:index])
	if normalizeURLCandidate(urlPart) == "" {
		return "", "", false
	}

	return urlPart, userPart, true
}

func normalizeURLCandidate(input string) string {
	cleaned := strings.TrimSpace(strings.ToValidUTF8(input, ""))
	cleaned = strings.NewReplacer("\r", "", "\n", "", "\t", "", " ", "").Replace(cleaned)
	cleaned = strings.Trim(cleaned, "|:;")
	if cleaned == "" {
		return ""
	}

	cleaned = collapseDuplicateSchemes(cleaned)
	lower := strings.ToLower(cleaned)
	if !strings.HasPrefix(lower, "https://") &&
		!strings.HasPrefix(lower, "http://") &&
		!strings.HasPrefix(lower, "ftp://") &&
		!strings.HasPrefix(lower, "sftp://") {
		if match := domainPattern.FindStringIndex(cleaned); match != nil && match[0] == 0 {
			switch {
			case strings.HasPrefix(lower, "ftp."):
				cleaned = "ftp://" + cleaned
			case strings.HasPrefix(lower, "sftp."):
				cleaned = "sftp://" + cleaned
			default:
				cleaned = "https://" + cleaned
			}
		}
	}

	cleaned = collapseDuplicateSchemes(cleaned)
	if match := domainPattern.FindStringIndex(cleaned); match == nil || match[0] != 0 {
		return ""
	}

	return cleaned
}

func collapseDuplicateSchemes(input string) string {
	replacer := strings.NewReplacer(
		"https://https://", "https://",
		"http://http://", "http://",
		"https://http://", "https://",
		"http://https://", "http://",
		"ftp://ftp://", "ftp://",
		"sftp://sftp://", "sftp://",
	)

	for {
		updated := replacer.Replace(input)
		if updated == input {
			return updated
		}
		input = updated
	}
}

func findLastCredentialSeparator(line string, limit int) int {
	if limit > len(line) {
		limit = len(line)
	}

	for i := limit - 1; i >= 0; i-- {
		switch line[i] {
		case '|', ';':
			return i
		case ':':
			if i+2 < len(line) && line[i+1] == '/' && line[i+2] == '/' {
				continue
			}
			return i
		}
	}
	return -1
}

func cleanCredentialToken(token string) string {
	token = strings.TrimSpace(strings.ToValidUTF8(token, ""))
	token = strings.Trim(token, "|:;/")
	return strings.TrimSpace(token)
}

func isLikelyUserToken(token string) bool {
	token = cleanCredentialToken(token)
	if token == "" || len(token) > 320 {
		return false
	}
	if strings.Contains(token, "://") || strings.ContainsAny(token, "/\\ \r\n\t") {
		return false
	}

	for _, r := range token {
		if unicode.IsLetter(r) || unicode.IsDigit(r) {
			return true
		}
	}
	return false
}

func isLikelyPasswordToken(token string) bool {
	token = strings.TrimSpace(strings.ToValidUTF8(token, ""))
	token = strings.Trim(token, "|:;")
	if token == "" || len(token) > 512 {
		return false
	}
	return !strings.ContainsAny(token, " \r\n\t")
}

func trimJoinedURL(urlPart string) string {
	urlPart = strings.TrimSpace(strings.ToValidUTF8(urlPart, ""))
	urlPart = strings.TrimRight(urlPart, "|:")
	if strings.HasSuffix(urlPart, "/") {
		trimmed := strings.TrimRight(urlPart, "/")
		if trimmed == "" {
			return urlPart
		}

		afterScheme := trimmed
		if index := strings.Index(afterScheme, "://"); index >= 0 {
			afterScheme = afterScheme[index+3:]
		}
		if strings.Contains(afterScheme, "/") {
			urlPart = trimmed
		}
	}
	return urlPart
}

func matchCMSRule(rules []CMSRule, line string) *CMSRule {
	lowerLine := strings.ToLower(line)
	compactLine := strings.ReplaceAll(lowerLine, " ", "")

	for i := range rules {
		rule := &rules[i]
		if rule.IsRegex {
			for _, compiled := range rule.compiledRegex {
				if compiled.MatchString(line) {
					return rule
				}
			}
		}

		for _, pattern := range rule.plainPatterns {
			if pattern == "" {
				continue
			}
			if strings.Contains(lowerLine, pattern) || strings.Contains(compactLine, pattern) {
				return rule
			}
		}
	}

	return nil
}

func isExpectedUgrepExit(err error) bool {
	var exitErr *exec.ExitError
	if !errors.As(err, &exitErr) {
		return false
	}
	return exitErr.ExitCode() == 1
}

func randomString(length int) (string, error) {
	if length <= 0 {
		return "", nil
	}

	const charset = "abcdefghijklmnopqrstuvwxyz0123456789"
	randomBytes := make([]byte, length)
	if _, err := rand.Read(randomBytes); err != nil {
		return "", fmt.Errorf("failed to generate random id: %w", err)
	}

	result := make([]byte, length)
	for i, value := range randomBytes {
		result[i] = charset[int(value)%len(charset)]
	}

	return string(result), nil
}

func indexHandler(w http.ResponseWriter, r *http.Request) {
	http.ServeFile(w, r, filepath.Join(".", "index.html"))
}

func baseName(path string) string {
	trimmed := strings.TrimRight(path, `\/`)
	if trimmed == "" {
		return path
	}
	idx := strings.LastIndexAny(trimmed, `\/`)
	if idx == -1 {
		return trimmed
	}
	return trimmed[idx+1:]
}

func sampleOffsets(size int64) []int64 {
	offsets := []int64{0}
	if size > sampleChunkSize*2 {
		offsets = append(offsets, maxInt64(0, size/2-sampleChunkSize/2))
	}
	if size > sampleChunkSize*4 {
		offsets = append(offsets, maxInt64(0, size-sampleChunkSize))
	}

	unique := make([]int64, 0, len(offsets))
	seen := make(map[int64]struct{}, len(offsets))
	for _, offset := range offsets {
		if _, ok := seen[offset]; ok {
			continue
		}
		seen[offset] = struct{}{}
		unique = append(unique, offset)
	}
	return unique
}

func formatSize(size int64) string {
	value := float64(size)
	unit := "B"

	switch {
	case size >= 1<<40:
		value = value / float64(1<<40)
		unit = "TB"
	case size >= 1<<30:
		value = value / float64(1<<30)
		unit = "GB"
	case size >= 1<<20:
		value = value / float64(1<<20)
		unit = "MB"
	case size >= 1<<10:
		value = value / float64(1<<10)
		unit = "KB"
	}

	if unit == "B" {
		return fmt.Sprintf("%d %s", size, unit)
	}
	return fmt.Sprintf("%.2f %s", value, unit)
}

func formatLineEstimate(total int64) string {
	switch {
	case total >= 1_000_000_000_000:
		return fmt.Sprintf("%.2f Triliun", float64(total)/1_000_000_000_000)
	case total >= 1_000_000_000:
		return fmt.Sprintf("%.2f Miliar", float64(total)/1_000_000_000)
	case total >= 1_000_000:
		return fmt.Sprintf("%.2f Juta", float64(total)/1_000_000)
	default:
		return strconv.FormatInt(total, 10)
	}
}

func formatETA(d time.Duration) string {
	if d <= 0 {
		return "0s"
	}

	seconds := int(d.Round(time.Second) / time.Second)
	hours := seconds / 3600
	minutes := (seconds % 3600) / 60
	secs := seconds % 60

	switch {
	case hours > 0:
		return fmt.Sprintf("%dh %dm %ds", hours, minutes, secs)
	case minutes > 0:
		return fmt.Sprintf("%dm %ds", minutes, secs)
	default:
		return fmt.Sprintf("%ds", secs)
	}
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func maxInt(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func minInt64(a, b int64) int64 {
	if a < b {
		return a
	}
	return b
}

func maxInt64(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
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
	http.HandleFunc("/results", resultsHandler)
	http.HandleFunc("/status", statusHandler)
	http.HandleFunc("/stats", statsHandler)
	http.HandleFunc("/filter-status", filterStatusHandler)

	log.Printf("server running at http://localhost:%s", port)
	log.Fatal(http.ListenAndServe(":"+port, nil))
}
