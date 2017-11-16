#include <stdio.h> 
#include <stddef.h> 
#include <assert.h> 
int y=0;
int main() {
  assert(sizeof(long)==sizeof(int*));
  long x=0;
  int *p = (int *)x;
  // is the value of p a null pointer?
  _Bool b1 = (p == NULL);// guaranteed to be true?
  _Bool b2 = (p == &y);  // guaranteed to be false?
  printf("(p==NULL)=%s  (p==&y)=%s\n", b1?"true":"false", 
         b2?"true":"false");
}
