#include <stdio.h>
typedef struct { int i1; float f1; } st1;
typedef struct { int i2; st1 s2; } st2;
int main() {
  st2 s = {.i2=2, .s2={.i1=1, .f1=1.0 } };
  int *p = &(s.i2), *q = &(s.s2.i1);
  _Bool b = (p < q); // does this have defined behaviour?
  printf("Addresses: p=%p  q=%p\n",(void*)p,(void*)q);
  printf("(p<q) = %s\n", b?"true":"false");
}
