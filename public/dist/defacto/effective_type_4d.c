#include <stdio.h>
#include <stdlib.h>
#include <string.h>
void user_memcpy(unsigned char* dest, 
                 unsigned char *src, size_t n) {
  while (n > 0)  {		
    *dest = *src;
    src += 1; dest += 1; n -= 1;
  }
}
int main() {
  int i=1;
  void *p = malloc(sizeof(int));
  user_memcpy((unsigned char*)p, (unsigned char*)(&i), sizeof(int));
  int *q = (int*)p;
  int j=*q;
  printf("j=%d\n",j);
}
