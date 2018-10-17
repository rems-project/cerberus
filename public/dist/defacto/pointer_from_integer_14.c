#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
int main() {
  int *xp=(int*)malloc(sizeof(int));
  *xp=1;
  uintptr_t i = (uintptr_t)xp;
  int *xp2 = (int*)i;
  free((void*)xp);
  int *yp=(int*)malloc(sizeof(int));
  *yp=2;
  uintptr_t j = (uintptr_t)yp;
  printf("Addresses: &i=%"PRIxPTR"  j=%"PRIxPTR"\n",i,j);
  if (i == j) {
    *xp2=3;
    printf("*yp=%d\n",*yp);
  }
}
