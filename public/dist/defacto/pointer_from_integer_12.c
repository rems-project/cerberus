#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stdint.h>
int main() {
  int *xp=(int*)malloc(sizeof(int));
  int *yp=(int*)malloc(sizeof(int));
  *xp=1;
  *yp=2;
  uintptr_t i = (uintptr_t)xp;
  free((void*)xp);
  int *xq=(int*)i;  // is this defined behaviour?
  if (xq == yp) 
    printf("equal\n");
  else 
    printf("nonequal\n");
}
