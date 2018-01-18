#include <stdio.h>
static int i = 2 || 1 / 0;

int main(void)
{
  printf("%d\n", i);
}
