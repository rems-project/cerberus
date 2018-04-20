#include <stdio.h>
typedef struct { int  i1; float f1; } st1;
typedef struct { int  i2; float f2; } st2;
int main() {
  st1 s1 = {.i1 = 1, .f1 = 1.0 };
  st2 s2;
  s2 = s1; 
  printf("s2.i2=%i2  s2.f2=%f\n",s2.i2,s2.f2);
}
