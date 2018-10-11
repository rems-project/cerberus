#include <stdio.h>
#include <string.h> 
#include <stdlib.h>
#include <stdint.h>
int main() {
  //size_t half=0x80;
  size_t half=SIZE_MAX / 2 + 1;
  printf("half = %zx\n",half);
  char *p = malloc(half);
  char *q = malloc(half);
  if (p!=NULL && q!=NULL) {
    *q = 0;
    uintptr_t v = ((uintptr_t)p == 0x00) ? half : 0x00;
    *(char*)v = 1;
    printf("*q = %x\n",(int)*q); // prints 1
  } else {
    printf("allocation failed\n");
  }
}
