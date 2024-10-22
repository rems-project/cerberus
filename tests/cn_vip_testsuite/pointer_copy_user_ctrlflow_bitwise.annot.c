#include "refinedc.h"

//CN_VIP #include <stdio.h>
#include <inttypes.h>
#include <limits.h>

#include <stddef.h>
#include "cn_lemmas.h"
int x=1;
int main()
/*CN_VIP*//*@ accesses x; @*/
{
  int *p = &x;
  uintptr_t i = (uintptr_t)p;
  //CN_VIP  int uintptr_t_width = sizeof(uintptr_t) * CHAR_BIT;
  /*CN_VIP*/size_t uintptr_t_width = sizeof(uintptr_t) * (size_t) CHAR_BIT;
  uintptr_t bit, j;
  j=0;
  /*CN_VIP*/int *q = NULL;
  /*CN_VIP*/bit=0;
  for (int k=0; k<uintptr_t_width; k++)
  /*@ inv i == (u64) p;
          ptr_eq(p, &x);
          uintptr_t_width == 64u64;
          (0i32 <= k) && (k <= 64i32);
          let k_mask = shift_left(1u64, (u64) k) - 1u64;
          j == bw_and_uf(i, k_mask);
  @*/
  {
    bit = (i & (((uintptr_t)1) << k)) >> k;
    if (bit == 1)
      j = j | ((uintptr_t)1 << k);
    else
      j = j;
  }
#if defined(ANNOT)
  q = copy_alloc_id(j, &x);
#else
  q = (int *)j;
#endif
  *q = 11; // is this free of undefined behaviour?
  /*CN_VIP*//*@ assert(*p == 11i32 && *q == 11i32); @*/
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
}
