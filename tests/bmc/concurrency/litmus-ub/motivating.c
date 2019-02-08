#include <stdint.h>
int x = 1, y = 2;
int a[20];
int main(void) {
 __BMC_ASSUME( (intptr_t)&x == 4 && (intptr_t)&y == 8 );
 if (&x+1 != &y) {
   {-{ {
     a[(intptr_t)(&x+1)] = 1;
   } ||| {
     a[(intptr_t)&y] = 2;
   } }-}
 }
 return a[8];
}
