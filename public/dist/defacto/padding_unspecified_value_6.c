#include <stdio.h>
#include <stddef.h>
void g(char *c, float *f) {
  *c='A';
  *f=1.0;
}
typedef struct { char c; float f; int i; } st;
int main() {
  // check there is a padding byte between c and f
  size_t offset_padding = offsetof(st,c)+sizeof(char);
  if (offsetof(st,f)>offset_padding) {
      st s; 
      unsigned char *p = 
        ((unsigned char*)(&s)) + offset_padding;
      *p = 'D';
      g(&s.c, &s.f);
      unsigned char c4 = *p; 
      // does c4 hold 'D', not an unspecified value?
      printf("c4=%c\n",c4);
  }
  return 0;
}

