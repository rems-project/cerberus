#include <stdio.h>
#include <string.h>
int  x=1;
void user_memcpy(unsigned char* dest, 
                 unsigned char *src, size_t n) {
  while (n > 0)  {		
    *dest = *src;
    src += 1;
    dest += 1;
    n -= 1;
  }
}
int main() {
  int *p = &x;
  int *q;
  user_memcpy((unsigned char*)&q, 
              (unsigned char*)&p, sizeof(int *));
  *q = 11; // is this free of undefined behaviour?
  printf("*p=%d  *q=%d\n",*p,*q);
}
