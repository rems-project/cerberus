#ifndef _TIME_H_
#define _TIME_H_

// 7.27#2
#ifndef NULL
#define NULL __cerbvar_NULL
#endif

#define CLOCKS_PER_SEC    1000000L
#define TIME_UTC          1

// 7.27#3
typedef __cerbty_size_t  size_t;

// NOTE: This is implementation defined
// Using x86_64 MacOS Darwin 18.0.0
typedef unsigned long    clock_t;
typedef long             time_t;

// 7.27#3
struct timespec {
  time_t tv_sec; // whole seconds -- >= 0
  long   tv_nsec; // nanoseconds -- [0, 999999999]
};

struct tm {
  int tm_sec;   /* seconds after the minute [0-60] */
  int tm_min;   /* minutes after the hour [0-59] */
  int tm_hour;  /* hours since midnight [0-23] */
  int tm_mday;  /* day of the month [1-31] */
  int tm_mon;   /* months since January [0-11] */
  int tm_year;  /* years since 1900 */
  int tm_wday;  /* days since Sunday [0-6] */
  int tm_yday;  /* days since January 1 [0-365] */
  int tm_isdst; /* Daylight Savings Time flag */
  long  tm_gmtoff;  /* offset from UTC in seconds */
  char  *tm_zone; /* timezone abbreviation */
};

clock_t clock(void);
double difftime(time_t time1, time_t time0);
time_t mktime(struct tm *timeptr);
struct tm *localtime(const time_t *timer);
time_t time(time_t *timer);
int timespec_get(struct timespec *ts, int base);

char *asctime(const struct tm *timeptr);
char *ctime(const time_t *timer);
struct tm *gmtime(const time_t *timer);
struct tm *localtime(const time_t *timer);

size_t strftime(char * restrict s,
             size_t maxsize,
             const char * restrict format,
             const struct tm * restrict timeptr);

#include "posix/time.h"

#endif
