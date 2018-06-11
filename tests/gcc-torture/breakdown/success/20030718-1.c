#include "cerberus.h"
/* PR c/10320
   The function temp was not being emitted in a prerelease of 3.4 20030406. 
   Contributed by pinskia@physics.uc.edu */

static void temp();
int 
main (void)
{
        temp();
        return 0;
}
static void 
temp (void){}


