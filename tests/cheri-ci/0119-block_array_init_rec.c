#include <stdint.h>
#include <stdio.h>
int main(void)
{
  intptr_t a[] = {(intptr_t)&a, 0, 0}; // THIS SHOULD WORK
}
