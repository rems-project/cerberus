#include <stdio.h>
#include <string.h>
int  x=1;
void user_memcpy2(unsigned char* dest, 
                  unsigned char *src, size_t n) {
  while (n > 0)  {		
    *dest = ((*src) ^ 1) ^ 1;
    src += 1;
    dest += 1;
    n -= 1;
  }
}
int main() {
  int *p = &x;
  int *q;
  user_memcpy2((unsigned char*)&q, (unsigned char*)&p, 
              sizeof(p));
  *q = 11; // is this free of undefined behaviour?
  printf("*p=%d  *q=%d\n",*p,*q);
}
