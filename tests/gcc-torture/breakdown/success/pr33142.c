#include "cerberus.h"
int abs(int j);

 int lisp_atan2(long dy, long dx) {
    if (dx <= 0)
        if (dy > 0)
            return abs(dx) <= abs(dy);
    return 0;
}

int 
main (void) {   
    volatile long dy = 63, dx = -77;
    if (lisp_atan2(dy, dx))
        abort();
    return 0;
}
