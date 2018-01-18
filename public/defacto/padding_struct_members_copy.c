#include <stdio.h>
#include <stddef.h>
#include <assert.h>
#include <inttypes.h>
typedef struct { char c; uint16_t u; } st;
int x;
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
  s2.c = s1.c;
  s2.u = s1.u;
  printf("*padding2=0x%x\n",(int)*padding2);
}
