#include <stdio.h>
typedef struct { int  i; float f; } st;
int main() {
  st s = {.i = 1, .f = 1.0};
  int *pi = &(s.i);
  st* p = (st*) pi; // free of undefined behaviour?
  p->f = 2.0;       // and this?
  printf("s.f=%f  p->f=%f\n",s.f,p->f);
}

