#include<stdio.h>

 // SHOULD PRINT "a >= b" TWICE
int main(void)
{
  signed int a   = -1;
  unsigned int b = 2;
  if (a < b)
    printf("a < b\n");
  else
    printf("a >= b\n");
  
  printf(a<b ? "a < b\n" : "a >= b\n");
}
