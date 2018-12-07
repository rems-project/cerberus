#ifndef _TIME_H_
#define _TIME_H_

// 7.27#2
#ifndef NULL
#define NULL __cerbvar_NULL
#endif


#define CLOCKS_PER_SEC

#define TIME_UTC

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

// 7.27.2.1
clock_t clock(void);

// 7.27.2.2
double difftime(time_t time1, time_t time0) { return time1 - time0; }

struct tm *localtime(const time_t *timer);

//#include "../posix/time.h"

#endif
