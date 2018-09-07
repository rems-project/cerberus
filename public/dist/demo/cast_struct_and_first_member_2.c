#include <stdio.h>
typedef struct { int  i; float f; } st;

void f(int *pi) {
  st *pst = (st*)pi;
  pst->f = 2.0; // free of undefined behaviour?
}
int main() {
  st s = {.i = 1, .f = 1.0};
  int *pi = &(s.i);
  f(pi);
  float f = s.f;
  printf("f=%f\n",f); // prints 2.0 not 1.0?
}

