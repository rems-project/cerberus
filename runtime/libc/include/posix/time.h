#ifndef _POSIX_TIME_H_
#define _POSIX_TIME_H_

#include <sys/types.h>

// Used in stdio.c
#define CLOCK_REALTIME           0
// char      *asctime(const struct tm *);
// char      *asctime_r(const struct tm *restrict, char *restrict);
// clock_t    clock(void);
// int        clock_getcpuclockid(pid_t, clockid_t *);
// int        clock_getres(clockid_t, struct timespec *);
int        clock_gettime(clockid_t, struct timespec *);
// int        clock_nanosleep(clockid_t, int, const struct timespec *, struct timespec *);
// int        clock_settime(clockid_t, const struct timespec *);
// char      *ctime(const time_t *);
// char      *ctime_r(const time_t *, char *);
// double     difftime(time_t, time_t);
// struct tm *getdate(const char *);
// struct tm *gmtime(const time_t *);
// struct tm *gmtime_r(const time_t *restrict, struct tm *restrict);
// struct tm *localtime(const time_t *);
// struct tm *localtime_r(const time_t *restrict, struct tm *restrict);
// time_t     mktime(struct tm *);
// int        nanosleep(const struct timespec *, struct timespec *);
// size_t     strftime(char *restrict, size_t, const char *restrict, const struct tm *restrict);
// size_t     strftime_l(char *restrict, size_t, const char *restrict, const struct tm *restrict, locale_t);
// char      *strptime(const char *restrict, const char *restrict, struct tm *restrict);
time_t     time(time_t *);
// int        timer_create(clockid_t, struct sigevent *restrict, timer_t *restrict);
// int        timer_delete(timer_t);
// int        timer_getoverrun(timer_t);
// int        timer_gettime(timer_t, struct itimerspec *);
// int        timer_settime(timer_t, int, const struct itimerspec *restrict, struct itimerspec *restrict);
// void       tzset(void);

#endif
