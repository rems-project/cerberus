#include <stdint.h>

// NOTE: the relevant part of the standard (§6.3.2.3#5) doesn't make this
// undefined, because the cast is between an integer and pointer type.
int main(void)
{
  int x;
  (int*)(((uintptr_t)&x) + 1); // Is this cast well defined?
}
