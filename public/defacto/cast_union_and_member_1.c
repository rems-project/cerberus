#include <stdio.h>
typedef union { int  i; float f; } un;
int main() {
  un u = {.i = 1};
  int *pi = &(u.i);
  un* p = (un*) pi; // free of undefined behaviour?
  p->f = 2.0;       // and this?
  printf("u.f=%f  p->f=%f\n",u.f,p->f);
}

