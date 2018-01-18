#include <stdio.h>
int main() {
  unsigned char c; 
  unsigned char *p=&c;
  unsigned char c2 = (c | 1);
  unsigned char c3 = (c2 & 1);
  // does c3 hold an unspecified value (not 1)?  
  printf("c=%i  c2=%i  c3=%i\n",(int)c,(int)c2,(int)c3);
}
