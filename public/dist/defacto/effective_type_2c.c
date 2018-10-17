#include <stdio.h>
typedef struct { int i; } st;
void f(st* sp, int* p) {
  sp->i = 2;
  *p = 3;
  printf("f: sp->i=%i  *p=%i\n",sp->i,*p); // prints 3,3 not 2,3 ?
}
int main() {
  st s = {.i = 1}; 
  st *sp = &s;
  int *p = &(s.i);
  f(sp, p); 
  printf("s.i=%i  sp->i=%i  *p=%i\n", s.i, sp->i, *p);
}

