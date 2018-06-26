#include "cerberus.h"
#define strcmp __builtin_strcmp
int 
main (void)
{
if(strcmp("X","X\376")>=0)abort();
exit(0);
}
