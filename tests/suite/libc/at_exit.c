#include <stdlib.h>
#include <stdio.h>

int x;

void f(void)
{
  printf("value: %d\n", x);
}

int main() {
  x = 42;
  atexit(f);
  exit(1);
}