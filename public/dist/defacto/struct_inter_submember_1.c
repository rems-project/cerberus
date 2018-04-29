#include <stdio.h>
#include <stddef.h>
struct S { int a[3]; int b[3]; } s;
int main() {
  s.b[2]=10;
  ptrdiff_t d;
  d = &(s.b[2]) - &(s.a[0]);  // defined behaviour?
  int *p;
  p = &(s.a[0]) + d;          // defined behaviour?
  *p = 11;                    // defined behaviour?
  printf("d=%td  s.b[2]=%d  *p=%d\n",d,s.b[2],*p);
}
