#include <errno.h>
#include <time.h>

double difftime(time_t time1, time_t time0) {
  return time1 - time0;
}

time_t time(time_t *timer) {
  return 0;
} // TODO

// POSIX

int clock_gettime(clockid_t clk, struct timespec *ts)
{
  // TODO:
  ts->tv_sec = 0;
  ts->tv_nsec = 0;
  return 0;
}