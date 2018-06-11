#include "cerberus.h"
int b = 0;

int 
func (void) { }

void
testit(int x)
{
  if (x != 20)
    abort ();
}

int 
main (void)

{
  int a = 0;

  if (b)
    func();

  /* simplify_and_const_int would incorrectly omit the mask in
     the line below.  */
  testit ((a + 23) & 0xfffffffc);
  exit (0);
}
