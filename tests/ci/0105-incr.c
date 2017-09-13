#include <stdio.h>

int main(void)
{
  int x[2] = {10,20}, *p = x;
  printf("*p++ ==> %d\n", *p++); // EXPECTING: "*p++ ==> 10\n"
  printf("*p   ==> %d\n", *p);   // EXPECTING: "*p   ==> 20\n"
}
