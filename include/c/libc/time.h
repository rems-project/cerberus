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
typedef __cerbty_clock_t clock_t;
typedef __cerbty_time_t  time_t;

// 7.27#3
struct timespec {
  time_t tv_sec; // whole seconds -- >= 0
  long   tv_nsec; // nanoseconds -- [0, 999999999]
}

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

long long __year_to_secs(long long year, int *is_leap)
{
  if (year-2ULL <= 136) {
    int y = year;
    int leaps = (y-68)>>2;
    if (!((y-68)&3)) {
      leaps--;
      if (is_leap) *is_leap = 1;
    } else if (is_leap) *is_leap = 0;
    return 31536000*(y-70) + 86400*leaps;
  }

  int cycles, centuries, leaps, rem;

  if (!is_leap) is_leap = &(int){0};
  cycles = (year-100) / 400;
  rem = (year-100) % 400;
  if (rem < 0) {
    cycles--;
    rem += 400;
  }
  if (!rem) {
    *is_leap = 1;
    centuries = 0;
    leaps = 0;
  } else {
    if (rem >= 200) {
      if (rem >= 300) centuries = 3, rem -= 300;
      else centuries = 2, rem -= 200;
    } else {
      if (rem >= 100) centuries = 1, rem -= 100;
      else centuries = 0;
    }
    if (!rem) {
      *is_leap = 0;
      leaps = 0;
    } else {
      leaps = rem / 4U;
      rem %= 4U;
      *is_leap = !rem;
    }
  }

  leaps += 97*cycles + 24*centuries - *is_leap;

  return (year-100) * 31536000LL + leaps * 86400LL + 946684800 + 86400;
}

int __month_to_secs(int month, int is_leap)
{
  static const int secs_through_month[] = {
    0, 31*86400, 59*86400, 90*86400,
    120*86400, 151*86400, 181*86400, 212*86400,
    243*86400, 273*86400, 304*86400, 334*86400 };
  int t = secs_through_month[month];
  if (is_leap && month >= 2) t+=86400;
  return t;
}

long long __tm_to_secs(const struct tm *tm)
{
  int is_leap;
  long long year = tm->tm_year;
  int month = tm->tm_mon;
  if (month >= 12 || month < 0) {
    int adj = month / 12;
    month %= 12;
    if (month < 0) {
      adj--;
      month += 12;
    }
    year += adj;
  }
  long long t = __year_to_secs(year, &is_leap);
  t += __month_to_secs(month, is_leap);
  t += 86400LL * (tm->tm_mday-1);
  t += 3600LL * tm->tm_hour;
  t += 60LL * tm->tm_min;
  t += tm->tm_sec;
  return t;
}

time_t mktime(struct tm *tm)
{
  struct tm new;
  long opp;
  long long t = __tm_to_secs(tm);

  __secs_to_zone(t, 1, &new.tm_isdst, &new.__tm_gmtoff, &opp, &new.__tm_zone);

  if (tm->tm_isdst>=0 && new.tm_isdst!=tm->tm_isdst)
    t -= opp - new.__tm_gmtoff;

  t -= new.__tm_gmtoff;
  if ((time_t)t != t) goto error;

  __secs_to_zone(t, 0, &new.tm_isdst, &new.__tm_gmtoff, &opp, &new.__tm_zone);

  if (__secs_to_tm(t + new.__tm_gmtoff, &new) < 0) goto error;

  *tm = new;
  return t;

error:
  // FIXME: add errno
  //errno = EOVERFLOW;
  //return -1;
}


struct tm *localtime(const time_t *timer);

//#include "../posix/time.h"

#else
#endif
