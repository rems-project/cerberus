#include <stdio.h>
#include <stddef.h>
typedef struct { char c; float f; int i; } st;
int main() {
  // check there is a padding byte between c and f
  size_t offset_padding = offsetof(st,c)+sizeof(char);
  if (offsetof(st,f)>offset_padding) {
      st s; 
      unsigned char *p = 
        ((unsigned char*)(&s)) + offset_padding;
      *p = 'B';
      s = (st){ .c='E', .f=1.0, .i=1};
      unsigned char c2 = *p; 
      // does c2 hold 'B', not an unspecified value?
      printf("c2=0x%x\n",(int)c2);
  }
  return 0;
}

