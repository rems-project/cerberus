#ifndef _SYS_TYPES_H_
#define _SYS_TYPES_H_

// NOTE: This is implementation defined
// Using x86_64 MacOS Darwin 18.0.0

#include <stdint.h>

typedef int64_t               blkcnt_t;
typedef int32_t               blksize_t;
typedef unsigned long         clock_t;
#define clockid_t             __cerbty_clockid_t
typedef int32_t               dev_t;
typedef unsigned int          fsblkcnt_t;
typedef unsigned int          fsfilcnt_t;
typedef uint32_t              gid_t;
typedef uint32_t              id_t;
typedef uint64_t              ino_t;
typedef int32_t               key_t;
typedef uint16_t              mode_t;
typedef int64_t               off_t;
typedef uint16_t              nlink_t; 
typedef int32_t               pid_t;
typedef uint32_t              sigset_t;
typedef uint32_t              uid_t;
typedef uint32_t              useconds_t;
typedef unsigned char         uuid_t[16];
typedef char                  uuid_string_t[37];
#define pthread_attr_t        __cerbty_pthread_attr_t
#define pthread_barrier_t     __cerbty_pthread_barrier_t
#define pthread_barrierattr_t __cerbty_pthread_barrierattr_t
#define pthread_cond_t        __cerbty_pthread_cond_t
#define pthread_condattr_t    __cerbty_pthread_condattr_t
#define pthread_key_t         __cerbty_pthread_key_t
#define pthread_mutex_t       __cerbty_pthread_mutex_t
#define pthread_mutexattr_t   __cerbty_pthread_mutexattr_t
#define pthread_once_t        __cerbty_pthread_once_t
#define pthread_rwlock_t      __cerbty_pthread_rwlock_t
#define pthread_rwlockattr_t  __cerbty_pthread_rwlockattr_t
#define pthread_spinlock_t    __cerbty_pthread_spinlock_t
#define pthread_t             __cerbty_pthread_t
typedef __cerbty_size_t       size_t;
typedef long                  ssize_t;
typedef int32_t               suseconds_t;
typedef long                  time_t;
#define timer_t               __cerbty_timer_t
#define trace_attr_t          __cerbty_trace_attr_t
#define trace_event_id_t      __cerbty_trace_event_id_t
#define trace_event_set_t     __cerbty_trace_event_set_t
#define trace_id_t            __cerbty_trace_id_t

#endif
