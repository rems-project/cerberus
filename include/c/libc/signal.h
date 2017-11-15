#ifndef	_SIGNAL_H_
#define	_SIGNAL_H_

typedef __cerbty_sig_atomic_t sig_atomic_t;
#define SIG_IGN __cerbvar_SIG_IGN
#define SIGILL  __cerbvar_SIGILL
#define SIGTERM __cerbvar_SIGTERM
#define SIG_DFL __cerbvar_SIG_DFL
#define SIGABRT __cerbvar_SIGABRT
#define SIGINT  __cerbvar_SIGINT
#define SIG_ERR __cerbvar_SIG_ERR
#define SIGFPE  __cerbvar_SIGFPE
#define SIGSEGV __cerbvar_SIGSEGV

void (*signal(int sig, void (*func)(int)))(int);
int raise(int sig);

#else
#endif
