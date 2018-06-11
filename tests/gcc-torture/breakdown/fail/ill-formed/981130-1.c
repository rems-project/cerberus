#include "cerberus.h"
/* { dg-xfail-if "alias analysis conflicts with instruction scheduling" { m32r-*-* } { "-O2" "-O1" "-O0" "-Os"} { "" } } */
struct s { int a; int b;};
struct s s1;
struct s s2 = { 1, 2, };

void 
check (int a, int b)
{
  if (a == b)
    exit (0);
  else
    abort ();
}

int 
main (void)
{
  int * p;
  int x;
  
  s1.a = 9;
  p    = & s1.a;
  s1   = s2;
  x    = * p;
  
  check (x, 1);
}


