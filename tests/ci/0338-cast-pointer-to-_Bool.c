#include <assert.h>
#include <stdlib.h>
#include <stdint.h>

int main(void)
{
  int x;
  uintptr_t ui = (uintptr_t)1234;
  assert (1 == (_Bool)&x);
  assert (1 == (_Bool)(int*)ui);
  assert (0 == (_Bool)NULL);
}