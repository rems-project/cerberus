// Example 2 from §6.7.9#25
#include <stdio.h>


int x[] = { 1, 3, 5 };

int main(void)
{
  printf("x[%lu] = {%d, %d, %d}\n",
         sizeof(x) / sizeof(int), x[0], x[1], x[2]);
}
