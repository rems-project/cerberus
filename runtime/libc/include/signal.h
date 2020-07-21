#ifndef _SIGNAL_H_
#define _SIGNAL_H_

typedef int sig_atomic_t;

void __sigdefault(int);
void __sigignore(int);
void __sigerror(int);

#define SIG_DFL __sigdefault
#define SIG_IGN __sigignore
#define SIG_ERR __sigerror

#define SIGABRT 0
#define SIGFPE  1
#define SIGILL  2
#define SIGINT  3
#define SIGSEGV 4
#define SIGTERM 5

#define SIGBUS  6
#define SIGHUP  7

void (*signal(int sig, void (*func)(int)))(int);
int raise(int sig);

#endif
