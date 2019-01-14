#include <stdlib.h>
#include <stdio.h>

int x;

void f(void)
{
  printf("value: %d\n", x);
}

int main() {
  x = 42;
  at_quick_exit(f);
  quick_exit(1);
}