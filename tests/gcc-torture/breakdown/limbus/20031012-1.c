#include "cerberus.h"
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

/* PR optimization/8750
   Used to fail under Cygwin with 
   -O2 -fomit-frame-pointer        
   Testcase by David B. Trout     */

#define STACK_SIZE 1000

#if defined(STACK_SIZE) && STACK_SIZE < 16000
#define ARRAY_SIZE (STACK_SIZE / 2)
#define STRLEN	   (ARRAY_SIZE - 9)
#else
#define ARRAY_SIZE 15000
#define STRLEN     13371
#endif

extern void *memset (void *, int, __SIZE_TYPE__);

static void 
foo (void)
{
    char a[ARRAY_SIZE];

    a[0]=0;
    memset( &a[0], 0xCD, STRLEN );
    a[STRLEN]=0;
    if (strlen(a) != STRLEN)
      abort ();
}

int main ( int argc, char* argv[] )
{
    foo();
    return 0;
}
