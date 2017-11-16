#include <stdio.h>
int  x=1, y=2;
int main() {
  int *p = &x + 1; 
  int *q = &y;
  _Bool b = (p == q); // free of undefined behaviour?
  printf("(p==q) = %s\n", b?"true":"false");
  return 0;
}
