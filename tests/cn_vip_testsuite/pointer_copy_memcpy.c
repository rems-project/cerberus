//CN_VIP #include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int x=1;
int main()
/*@ accesses x; @*/
{
  int *p = &x;
  int *q;
  /*CN_VIP*/if (&p == &q) return 0;                                         // CN used to derive disjointness and non-null
  /*CN_VIP*/if ((uintptr_t)&p + sizeof(int*) < (uintptr_t)&p) return 0;     // constraints from resource ownership, but this
  /*CN_VIP*/if ((uintptr_t)&q + sizeof(int*) < (uintptr_t)&q) return 0;     // was removed for performance reasons.
  /*CN_VIP*/unsigned char *q_bytes = block_int_ptr_to_block_uchar_arr(&q);
  /*CN_VIP*/unsigned char *p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  _memcpy (q_bytes, p_bytes, sizeof p);
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*p == 11i32 && *q == 11i32); @*/
}
