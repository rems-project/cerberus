#include "cerberus.h"
/* PR 15454 */

void abort ();
int 
main (void) {
        int foo;
        int bar (void)
        {
                int baz = 0;
                if (foo!=45)
                        baz = foo;
                return baz;
        }
        foo = 1;
        if (!bar ())
                abort ();
        return 0;
}
