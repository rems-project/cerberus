#include <stdio.h>
float fabs_single(float x) {
  union { float f; unsigned int i; } u;
  u.f = x;
  u.i = u.i & 0x7FFFFFFF;
  return u.f;  
}
int main() {
  float f=-1.0;
  float g;
  g = fabs_single(f);
  printf("g=%f\n",g);
}
