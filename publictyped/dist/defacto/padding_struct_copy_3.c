#include <stdio.h>
#include <stddef.h>
#include <assert.h>
#include <inttypes.h>
typedef struct { char c; uint16_t u; } st;
int x;
void f(st* s2p, st* s1p) {
  s2p->c = s1p->c;
  s2p->u = s1p->u;
}
int main() {
  // check there is a padding byte between c and u
  size_t offset_padding = offsetof(st,c)+sizeof(char);
  assert(offsetof(st,u)>offset_padding);
  st s1 = { .c = 'A', .u = 0x1234 };
  unsigned char *padding1 = 
    (unsigned char*)(&s1) + offset_padding;
  //  printf("*padding1=0x%x\n",(int)*padding1);
  *padding1 = 0xBA; 
  printf("*padding1=0x%x\n",(int)*padding1);
  st s2;
  unsigned char *padding2 = 
    (unsigned char*)(&s2) + offset_padding;
  printf("*padding2=0x%x\n",(int)*padding2);//warn 
  f(&s2,&s1);   //s2 = s1;
  printf("*padding2=0x%x\n",(int)*padding2);
}
