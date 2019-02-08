#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;
int T0_r2;

{-{
{ WRITE_ONCE(x,2);
smp_mb();
T0_r2 = READ_ONCE(y); }
|||
{ WRITE_ONCE(y,1);
smp_mb();
WRITE_ONCE(x,1); }
}-};
 assert(!(x == 2 && T0_r2 == 0));
}
