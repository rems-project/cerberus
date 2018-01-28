#ifndef	_TIME_H_
#define	_TIME_H_

typedef __cerbty_size_t      size_t;
typedef __cerbty_clock_t      clock_t;
typedef __cerbty_time_t      time_t;

struct tm *localtime(const time_t *timer);

#include "../posix/time.h"

#else
#endif
