#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <inttypes.h>
int main() {
  int *xp=malloc(sizeof(int));
  int *yp=malloc(sizeof(int));
  *xp=1;
  *yp=2;
  int *p = (int*) (((uintptr_t)xp) - 16);
  int *q = yp;
  printf("Addresses: xp=%p p=%p q=%p\n",
         (void*)xp,(void*)p,(void*)q);
  //  if (p == q) {
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // does this have undefined behaviour?
    printf("*xp=%d *yp=%d *p=%d *q=%d\n",*xp,*yp,*p,*q);
  }
  return 0;
}
