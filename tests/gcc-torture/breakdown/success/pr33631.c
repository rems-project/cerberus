#include "cerberus.h"
typedef union
{
  int __lock;
} pthread_mutex_t;


int 
main (void)
{
    struct { int c; pthread_mutex_t m; } r = { .m = 0 };
    if (r.c != 0)
      abort ();
    return 0;
}
