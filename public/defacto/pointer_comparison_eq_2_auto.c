#include <stdio.h>
#include <string.h> 
int main() {
  int  x=1;
  float f=1.0;
  int *p = (int *)&f; 
  float *q = &f;
  _Bool b = (p == q); // free of undefined behaviour?
  printf("(p==q) = %s\n", b?"true":"false");
  return 0;
}
