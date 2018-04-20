#include <stdio.h>
void f(char* cp, float*fp) {
  *cp='A';
  *fp=1.0;
}
typedef struct { char c; float f; } st;
int main() {
  st s1;
  f(&s1.c, &s1.f);
  st s2;
  s2 = s1;
  printf("s2.c=0x%x  s2.f=%f\n",s2.c,s2.f);
}

