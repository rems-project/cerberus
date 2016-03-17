#ifndef	_THREADS_H_
#define	_THREAD_H_

#define thread_local _Thread_local

#define ONCE_FLAG_INIT      __cerbvar_ONCE_FLAG_INIT
#define TSS_DTOR_ITERATIONS __cerbvar_TSS_DTOR_ITERATIONS

typedef __cerbty_cnd_t      cnd_t;
typedef __cerbty_thrd_t     thrd_t;
typedef __cerbty_tss_t      tss_t;
typedef __cerbty_mtx_t      mtx_t;

// TODO: wtf? typedef void (*)(void*) tss_dtor_t;
// TODO: wtf? typedef int (*)(void*)  thrd_start_t;

typedef __cerbty_once_flag once_flag;

#else
#endif
