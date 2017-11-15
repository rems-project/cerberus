#include <stdio.h>
#include <string.h> 
int  y[2], x[2];
int main() {
  int *p = &x[1] + (&y[1]-&y[0]) + 0;
  int *q = &y[0];
  printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // does this have undefined behaviour?
    printf("y[0]=%d *p=%d *q=%d\n",y[0],*p,*q);
  }
  return 0;
}
