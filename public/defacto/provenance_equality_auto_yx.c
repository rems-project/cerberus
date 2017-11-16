#include <stdio.h>
#include <string.h> 
int main() {
  int  y=2, x=1;
  int *p = &x + 1;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  _Bool b = (p==q);
  printf("(p==q) = %s\n", b?"true":"false");
  return 0;
}
