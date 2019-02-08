#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;

int T1_r1;
int T1_r2;
{-{
{ WRITE_ONCE(x,1);
smp_wmb();
WRITE_ONCE(y,1); }
|||
{ T1_r1 = READ_ONCE(y);
smp_rmb();
T1_r2 = READ_ONCE(x); }
}-};
 assert(!(T1_r1 == 1 && T1_r2 == 0));
}
