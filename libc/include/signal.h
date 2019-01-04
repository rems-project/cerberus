#ifndef	_SIGNAL_H_
#define	_SIGNAL_H_

typedef __cerbty_sig_atomic_t sig_atomic_t;
#define SIG_IGN 1 //__cerbvar_SIG_IGN
#define SIGILL  2 //__cerbvar_SIGILL
#define SIGTERM 3 //__cerbvar_SIGTERM
#define SIG_DFL 4 //__cerbvar_SIG_DFL
#define SIGABRT 5 //__cerbvar_SIGABRT
#define SIGINT  6 //__cerbvar_SIGINT
#define SIG_ERR 7 //__cerbvar_SIG_ERR
#define SIGFPE  8 //__cerbvar_SIGFPE
#define SIGSEGV 9 //__cerbvar_SIGSEGV

// TODO: not sure about these signals
#define SIGBUS  10 //__cerbvar_SIGBUS
#define SIGHUP  11

void (*signal(int sig, void (*func)(int)))(int);
int raise(int sig);

#else
#endif
