#include <stdio.h>
int main() {
  int x;
  unsigned char *p = (unsigned char*)&x;
  //is this free of undefined behaviour?
  unsigned char *q = p + 11;
  q = q - 10;
  *q = 1;
  printf("x=0x%x  *p=0x%x  *q=0x%x\n",x,*p,*q);
}

