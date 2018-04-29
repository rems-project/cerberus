#include <stdio.h>
typedef struct { int i; float f; } st;
int main() {
  st s = {.i=1, .f=1.0 };
  int *p = &(s.i);
  float *q = &(s.f);
  _Bool b = (p < q); // does this have defined behaviour?
  printf("Addresses: p=%p  q=%p\n",(void*)p,(void*)q);
  printf("(p<q) = %s\n", b?"true":"false");
}
