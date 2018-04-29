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
      *p = 0;
      s.c = 'A';
      s.f = 1.0;
      s.i = 42;
      unsigned char c3 = *p; 
      // does c3 hold 0, not an unspecified value?
      printf("c3=0x%x\n",c3);
  }
  return 0;
}

