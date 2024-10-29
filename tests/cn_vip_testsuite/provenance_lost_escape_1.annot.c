#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "charon_address_guesses.h"
#include "cn_lemmas.h"
int x=1; // assume allocation ID @1, at ADDR_PLE_1
int main()
/*@ accesses x; @*/
{
  int *p = &x;
  uintptr_t i1 = (intptr_t)p;            // (@1,ADDR_PLE_1)
  uintptr_t i2 = i1 & 0x00000000FFFFFFFF;//
  uintptr_t i3 = i2 & 0xFFFFFFFF00000000;// (@1,0x0)
  uintptr_t i4 = i3 + ADDR_PLE_1;        // (@1,ADDR_PLE_1)
  /*@ apply assert_equal(i4, (u64)&x); @*/
#ifdef ANNOT
  int *q = copy_alloc_id(i4, p);
#else
  int *q = (int *)i4;
#endif
  //CN_VIP printf("Addresses: p=%p\n",(void*)p);
  /*CN_VIP*//*@ to_bytes Owned<uintptr_t>(&i1); @*/
  /*CN_VIP*//*@ to_bytes Owned<uintptr_t>(&i4); @*/
  /*CN_VIP*/int result = _memcmp((unsigned char*)&i1, (unsigned char*)&i4, sizeof(i1));
  /*CN_VIP*//*@ from_bytes Owned<uintptr_t>(&i1); @*/
  /*CN_VIP*//*@ from_bytes Owned<uintptr_t>(&i4); @*/
  if (result == 0) {
    *q = 11;  // does this have defined behaviour?
    /*CN_VIP*//*@ assert(x == 11i32 && *p == 11i32 && *q == 11i32); @*/
    //CN_VIP printf("x=%d *p=%d *q=%d\n",x,*p,*q);
  }
}
