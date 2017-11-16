#include <stdio.h>
void* memcpy(void *dest,const void *src,size_t n) {
  unsigned long i; 
  for (i=0; i<n; i++)
    ((char *)dest)[i] = ((const char *) src)[i];
  return dest;
}
int main () {
  int x[2], y[2];
  x[0] = 0; x[1] = 1;
  memcpy(y, x, sizeof(x));
  printf("y[0]=%i y[1]=%i\n",y[0],y[1]);
}
