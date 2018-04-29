#include <stdio.h>
#include <string.h> 
int  x=1, y=2;
void f(int* p, int* q);
int main() {
  int *p = &x + 1;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  f(p,q);
  return 0;
}
