#include "refinedc.h"

#include <stdio.h>
#include <string.h> 
#include <stdint.h>
#include <inttypes.h>
int y=2, x=1;
int main() {
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
  if (memcmp(&p, &q, sizeof(p)) == 0) {
#if defined(ANNOT)
    int *r = copy_alloc_id(i, q);
#else
    int *r = (int *)i;
#endif
    *r=11;
    r=r-1;  // is this free of UB?
    *r=12;  // and this?    
    printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r); 
  }
}

/* NOTE: vip_artifact/evaluation_cerberus/results.pdf expects for this test:

   |----------------------+----------------------+--------------+--------------|
   | PNVI-ae-udi no annot | PNVI-ae-udi w/ annot | VIP no annot | VIP w/ annot |
   |----------------------+----------------------+--------------+--------------|
   | UB: line 19          | UB: line 19          | UB: line 19  | UB: line 20  |
   |----------------------+----------------------+--------------+--------------|

   This doesn't make sense, because (a) comments don't line up with numbers and (b)

   PNVI-ae-udi no annot: prov is symbolic (one-past int to pointer),
                         collapses to q on store, so UB on line 20
   PNVI-ae-udi w/ annot: prov is copy_alloc_id to @q, so UB on line 20
           VIP no annot: prov is round-trip preserved to @p, so UB on line 19
           VIP w/ annot: prov is copy_alloc_id @q, so UB on line 20
*/
