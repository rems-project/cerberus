#include "cerberus.h"
struct decision
{
  char enforce_mode;             
  struct decision *next;         
};


static void 
clear_modes (register struct decision *p)
{
  goto blah;

foo:
  p->enforce_mode = 0;
blah:
  if (p)
    goto foo;
}

int 
main (void)
{
  struct decision *p = 0;
  clear_modes (p);
  exit (0);
}
