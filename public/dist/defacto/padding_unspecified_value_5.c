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
      *p = 'C';
      s.i = 42;
      unsigned char c3 = *p; 
      // does c3 hold 'C', not an unspecified value?
      printf("c3=%c\n",c3);
  }
  return 0;
}

