//CN_VIP #include <stdio.h>
//CN_VIP #include <string.h>
#include <stddef.h>
#include <inttypes.h>
#include "cn_lemmas.h"
int  x=1;
void user_memcpy(unsigned char *dest,
                 unsigned char *src, size_t n)
/*@
requires
    take Src = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { W<unsigned char>(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(dest, i)) };
    Src == SrcR;
    each (u64 i; 0u64 <= i && i < n ) { SrcR[i] == DestR[i] };
@*/
{
  while (n > 0u)
  /*@
  inv
    let src_start = {src}@start;
    let dest_start = {dest}@start;
    let n_start = {n}@start;
    0u64 <= n; n <= n_start;
    src == array_shift<unsigned char>(src_start, n_start - n);
    dest == array_shift<unsigned char>(dest_start, n_start - n);
    take S = each (u64 i; 0u64 <= i && i < n_start ) { RW(array_shift(src_start, i)) };
    Src == S;
    take D1 = each (u64 i; n_start - n <= i && i < n_start ) { W<unsigned char>(array_shift(dest_start, i)) };
    take D2 = each (u64 i; 0u64 <= i && i < n_start - n ) { RW(array_shift(dest_start, i)) };
    each (u64 i; 0u64 <= i && i < n_start - n ) { S[i] == D2[i] };
  @*/
  {
    /*@ focus RW<unsigned char>, n_start - n; @*/
    /*@ focus W<unsigned char>, n_start - n; @*/
    *dest = *src;
    src += 1; dest += 1; n -= 1u;
  }
}
int main()
/*CN_VIP*//*@ accesses x; @*/
{
  int *p = &x;
  int *q;
  /*CN_VIP*//*@ to_bytes RW<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes W<int*>(&q); @*/
  user_memcpy((unsigned char*)&q, (unsigned char*)&p, sizeof(int *));
  /*CN_VIP*//*@ apply byte_arrays_equal(&q, &p, sizeof<int*>); @*/
  /*CN_VIP*//*@ from_bytes RW<int*>(&q); @*/
  /*CN_VIP*//*@ from_bytes RW<int*>(&p); @*/
#ifdef NO_ROUND_TRIP
  /*CN_VIP*/q = __cerbvar_copy_alloc_id((uintptr_t)q, &x);
  /*CN_VIP*/p = __cerbvar_copy_alloc_id((uintptr_t)p, &x);
#endif
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*q == 11i32 && *p == 11i32); @*/
}
