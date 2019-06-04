#include <stdio.h>
#include "signal.h"

#define NUMSIG 8    // Number of signals

char *signame[] = {
  "SIGABRT", "SIGFPE", "SIGILL",
  "SIGINT", "SIGSEGV", "SIGTERM",
  "SIGBUS", "SIGHUP"
};

void (*sighandler[])(int) = {
  SIG_ERR, SIG_ERR, SIG_IGN,
  SIG_IGN, SIG_ERR, SIG_ERR,
  SIG_DFL, SIG_DFL
};

void __sigdefault (int sig)
{
  if (sig >= 0 && sig < sizeof(signame))
    fprintf(stderr, ">> Signal %s was raised.\n", signame[sig]);
  else
    fprintf(stderr, ">> An unknown signal was raised.\n");
}

void __sigignore (int sig)
{
  // DO NOTHING
}

void __sigerror(int sig)
{
  if (sig >= 0 && sig < sizeof(signame))
    fprintf(stderr, "%s\n", signame[sig]);
  else
    fprintf(stderr, "SIG_ERR\n");
}

// TODO: When #103 is fixed, should uncomment this
//void (*signal(int sig, void (*func)(int)))(int)
typedef void (*Fun)(int);
Fun signal(int sig, Fun func)
{
  if (sig >= 0 && sig < NUMSIG) {
    sighandler[sig] = func;
    return func;
  }
  return SIG_ERR;
}

int raise(int sig)
{
  if (sig >= 0 && sig < NUMSIG) {
    sighandler[sig](sig);
    return 0;
  }
  return 1;
}
