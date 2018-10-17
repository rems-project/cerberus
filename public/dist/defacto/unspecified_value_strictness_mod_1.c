#include <stdio.h>
int main() {
  unsigned char c; 
  unsigned char *p=&c;
  unsigned char c2 = (c % 2u);
  // can reading c2 give something other than 0 or 1?
  printf("c=%i  c2=%i\n",(int)c,(int)c2);
}
