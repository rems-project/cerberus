#include <stdio.h>
#include <string.h>
typedef struct { int i; float f; } st;
st s1 = {.i=1, .f=1.0 };
st s2;
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
  st *p = &s1;
  st *q = &s2;
  user_memcpy((unsigned char*)q, 
              (unsigned char*)p, sizeof(st));
  // is this free of undefined behaviour?
  printf("p->i = %d  q->i = %d\n",p->i,q->i);
}
