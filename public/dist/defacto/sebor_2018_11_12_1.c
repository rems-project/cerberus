//  extern uintptr_t offset;
#include <stdint.h>
uintptr_t offset=4;

void f (void)
{
  int x = 1, y = 2;
  
  int save_y = y;
  
  uintptr_t ux = (uintptr_t)&x;
  uintptr_t uy = (uintptr_t)&y;
  
  int *p = (int *)(ux + offset);
  int *q = &y;
  
  if (p == q)   // must be assumed to be true in PNVI
    {           // may be assumed to be false in PVI
      *p = 11;
      
      // allowed not to abort in PVI
      // but must abort in PNVI
      assert (y == save_y);
    }
}

int main(void)
{
  f();
}
