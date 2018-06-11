#include "cerberus.h"
/* { dg-require-effective-target trampolines } */

int 
main (void)
{
  void p(void ((*f) (void ())))
    {
      void r()
	{
	  foo ();
	}

      f(r);
    }

  void q(void ((*f)()))
    {
      f();
    }

  p(q);

  exit(0);
}

int 
foo (void){}
