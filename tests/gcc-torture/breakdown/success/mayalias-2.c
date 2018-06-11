#include "cerberus.h"
typedef struct  { short x; } test;

int 
f (void) {
  int a=10;
  test *p=(test *)&a;
  p->x = 1;
  return a;
}

int 
main (void) {
  if (f() == 10)
    __builtin_abort();
  return 0;
}


