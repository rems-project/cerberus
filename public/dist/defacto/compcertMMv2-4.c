#include <stdio.h>
unsigned int bswap(unsigned int x) {
  union { unsigned int i; char c[4];} src, dst;
  int n;
  src.i=x;
  dst.c[3]=src.c[0]; dst.c[2]=src.c[1];
  dst.c[1]=src.c[2]; dst.c[0]=src.c[3];
  return dst.i;
}
int main() {
  unsigned int x=0x11223344;
  unsigned int y;
  y = bswap(x);
  printf("y=0x%x\n",y);
}
