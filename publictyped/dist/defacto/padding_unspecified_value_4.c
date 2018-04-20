#include <stdio.h>
#include <stddef.h>
#include <inttypes.h>
#include <assert.h>
typedef struct { char c; uint16_t u; } st;
int main() {
  // check there is a padding byte between c and u
  size_t offset_padding = offsetof(st,c)+sizeof(char);
  assert(offsetof(st,u)>offset_padding);
  st s; 
  unsigned char *p = 
    ((unsigned char*)(&s)) + offset_padding;
  *p = 'B';
  st s2 = { .c='E', .u=1};
  s = s2;
  unsigned char c = *p; 
  // does c hold 'B', not an unspecified value?
  printf("c=0x%x\n",(int)c);
  return 0;
}

