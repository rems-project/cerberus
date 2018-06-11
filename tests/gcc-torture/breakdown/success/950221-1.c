#include "cerberus.h"
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

struct parsefile
{
  long fd;
  char *buf;
};
struct parsefile basepf;
struct parsefile *parsefile = &basepf;
#ifdef STACK_SIZE
int filler[STACK_SIZE / (2*sizeof(int))];
#else
int filler[0x3000];
#endif
int el;

char *
g1 (int a, int *b)
{
}

int 
g2 (long a)
{
  if (a != 0xdeadbeefL)
    abort ();
  exit (0);
}

int 
f (void)
{
  register char *p, *q;
  register int i;
  register int something;

  if (parsefile->fd == 0L && el)
    {
      const char *rl_cp;
      int len;
      rl_cp = g1 (el, &len);
      strcpy (p, rl_cp);
    }
  else
    {
    alabel:
      i = g2 (parsefile->fd);
    }
}

int 
main (void)
{
  el = 0;
  parsefile->fd = 0xdeadbeefL;
  f ();
}
