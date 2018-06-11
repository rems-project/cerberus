#include "cerberus.h"
/* REPRODUCED:RUN:SIGNAL MACHINE:i386 OPTIONS:-O */
int 
main (void)
{
if(strcmp("X","")<0)abort();
exit(0);
}
