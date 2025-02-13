#include <cn-testing/size.h>

static size_t global_size = 20;

size_t cn_gen_get_size(void) {
  return global_size;
}

void cn_gen_set_size(size_t sz) {
  global_size = sz;
}

static size_t global_max_size = 25;

size_t cn_gen_get_max_size(void) {
  return global_max_size;
}

void cn_gen_set_max_size(size_t sz) {
  global_max_size = sz;
}

static uint16_t stack_depth = 0;
static uint16_t max_stack_depth = UINT8_MAX;

uint16_t cn_gen_depth() {
  return stack_depth;
}

uint16_t cn_gen_max_depth() {
  return max_stack_depth;
}

void cn_gen_set_max_depth(uint16_t msd) {
  max_stack_depth = msd;
}

void cn_gen_increment_depth() {
  stack_depth++;
}

void cn_gen_decrement_depth() {
  stack_depth--;
}

static uint16_t depth_failures_allowed = UINT16_MAX;

void cn_gen_set_depth_failures_allowed(uint16_t allowed) {
  depth_failures_allowed = allowed;
}

uint16_t cn_gen_get_depth_failures_allowed() {
  return depth_failures_allowed;
}

static uint16_t size_split_backtracks_allowed = 0;

void cn_gen_set_size_split_backtracks_allowed(uint16_t allowed) {
  size_split_backtracks_allowed = allowed;
}

uint16_t cn_gen_get_size_split_backtracks_allowed() {
  return size_split_backtracks_allowed;
}

static uint8_t timeout = 0;

void cn_gen_set_input_timeout(uint8_t seconds) {
  timeout = seconds;
}

uint8_t cn_gen_get_input_timeout(void) {
  return timeout;
}

static uint64_t timer = 0;

void cn_gen_set_input_timer(uint64_t time) {
  timer = time;
}

uint64_t cn_gen_get_input_timer(void) {
  return timer;
}

#if defined(__unix__) || (defined(__APPLE__) && defined(__MACH__))
  #include <sys/time.h>
#elif defined(_WIN32) || defined(_WIN64)
  #include <Windows.h>

/// Taken from https://stackoverflow.com/questions/10905892/equivalent-of-gettimeofday-for-windows
int gettimeofday(struct timeval* tp, struct timezone* tzp) {
  // Note: some broken versions only have 8 trailing zero's, the correct epoch has 9 trailing zero's
  // This magic number is the number of 100 nanosecond intervals since January 1, 1601 (UTC)
  // until 00:00:00 January 1, 1970
  static const uint64_t EPOCH = ((uint64_t)116444736000000000ULL);

  SYSTEMTIME system_time;
  FILETIME file_time;
  uint64_t time;

  GetSystemTime(&system_time);
  SystemTimeToFileTime(&system_time, &file_time);
  time = ((uint64_t)file_time.dwLowDateTime);
  time += ((uint64_t)file_time.dwHighDateTime) << 32;

  tp->tv_sec = (long)((time - EPOCH) / 10000000L);
  tp->tv_usec = (long)(system_time.wMilliseconds * 1000);
  return 0;
}
#endif

uint64_t cn_gen_get_milliseconds(void) {
  struct timeval tv;

  gettimeofday(&tv, NULL);
  return (((uint64_t)tv.tv_sec) * 1000) + (tv.tv_usec / 1000);
}
