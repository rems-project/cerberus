#include "cerberus.h"
/* PR tree-optimization/69097 */

int a, b;
unsigned int c;

int 
main (void)
{
  int d = b;
  b = ~(~a + (~d | b));
  a = ~(~c >> b);
  c = a % b;
  return 0;
}
