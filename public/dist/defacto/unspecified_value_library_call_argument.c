#include <stdio.h>
int main() 
{
  unsigned char c; 
  unsigned char *p = &c;
  printf("char 0x%x\n",(unsigned int)c);
  // does this have defined behaviour?
}

