#ifndef _SYS_TIME_H_
#define	_SYS_TIME_H_

// TODO fix parser ...
#ifndef _TIME_H_
typedef __cerbty_time_t      time_t;
#endif
typedef __cerbty_suseconds_t suseconds_t;

struct timeval {
  time_t      tv_sec;
  suseconds_t tv_usec;
};

int gettimeofday(struct timeval *restrict tp, void *restrict tzp);

// TODO: where does thi function come from?
void timersub(struct timeval *a, struct timeval *b, struct timeval *res);

#else
#endif
