#include <stdio.h>
int main() 
{
  unsigned char c; 
  unsigned char *p = &c;
  if (c == 'a') 
    printf("equal\n");
  else
    printf("nonequal\n");
  // does this have defined behaviour?
}

