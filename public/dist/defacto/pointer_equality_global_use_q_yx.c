#include <stdio.h>
#include <string.h> 
int y=2, x=1;
int main() {
  int *p = &x + 1;
  int *q = &y;
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  if (p==q) {
    printf("equal\n");
    *q=22;  // defined behaviour?
  }
  printf("x=%i y=%i\n",x,y);
}
