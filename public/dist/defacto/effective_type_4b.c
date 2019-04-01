#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main() {
  int i=1;
  void *p = malloc(sizeof(int));
  memcpy((void*)p, (const void*)(&i), sizeof(int));
  int *q = (int*)p;
  int j=*q;
  printf("j=%d\n",j);
}
