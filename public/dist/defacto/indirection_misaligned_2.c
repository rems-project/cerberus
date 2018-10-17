#include <stdint.h>

// According to §6.5.3.2#4 and footnote 102, the indirection of "an address
// inappropriately aligned for the type of object pointed to" is undefined.
// In this test, the address is well aligned for the type of the pointer, but
// misalignd for the type of the object in memory.
int main(void)
{
  int x;
  char* p = (char*)(((uintptr_t)&x) + 1);
  *p; // is this indirection undefined?
}
