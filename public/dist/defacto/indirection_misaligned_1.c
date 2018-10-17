#include <stdint.h>

// According to §6.5.3.2#4 and footnote 102, the indirection of "an address
// inappropriately aligned for the type of object pointed to" is undefined.
// In this test, the address is well aligned for the type of the object in
// memory, but not for the type of the pointer.
int main(void)
{
  char x[8];
  int* p = (int*)(((uintptr_t)&x) + 1);
  *p; // is this indirection undefined?
}
