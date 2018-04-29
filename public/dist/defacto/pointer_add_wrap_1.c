#include <stdio.h>
int main() {
  unsigned char x;
  unsigned char *p = &x;
  unsigned long long h = ( 1ull << 63 );
  //are the following free of undefined behaviour?
  unsigned char *q1 = p + h;
  unsigned char *q2 = q1 + h;
  printf("Addresses: p =%p  q1=%p\n",
         (void*)p,(void*)q1);
  printf("Addresses: q2=%p  h =0x%llx\n",
         (void*)q2,h);
}

