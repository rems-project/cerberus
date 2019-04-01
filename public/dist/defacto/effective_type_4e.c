#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main() {
  int i=1;
  void *p = malloc(sizeof(int));
  memcpy((void*)p, (const void*)(&i), sizeof(int));
  int k;
  for (k=0;k<sizeof(int);k++)
    *(((unsigned char*)p)+k)=0;
  int *q = (int*)p;
  int j=*q;
  printf("j=%d\n",j);
}
