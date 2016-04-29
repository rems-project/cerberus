#include <stdio.h>

int x = 1024;
int *p = &x;

int main(void)
{
  printf("BEFORE: %d\n", x);
  *p = 42;
  printf("AFTER: %d\n", x);
}
