#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;

int T1_r3;
int T2_r1;
int T2_r2;
{-{
{ WRITE_ONCE(y,1); }
|||
{ T1_r3 = READ_ONCE(y);
smp_mb();
WRITE_ONCE(x,1); }
|||
{ T2_r1 = READ_ONCE(x);
smp_rmb();
T2_r2 = READ_ONCE(y); }
}-};
 assert(!(T1_r3 == 1 && T2_r1 == 1 && T2_r2 == 0));
}
