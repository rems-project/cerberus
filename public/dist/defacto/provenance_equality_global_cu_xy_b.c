#include <stdio.h>
#include <string.h> 
extern int y,x;
void f(int* p, int* q) {
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  printf("(p==q) = %s\n", b?"true":"false");
  return;
}
