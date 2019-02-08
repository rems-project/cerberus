#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;


{-{
{ WRITE_ONCE(x,1);
smp_mb();
WRITE_ONCE(y,2); }
|||
{ WRITE_ONCE(y,1);
smp_mb();
WRITE_ONCE(x,2); }
}-};
 __BMC_ASSUME (x == 1 && y == 1);
}
