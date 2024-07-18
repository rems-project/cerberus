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
    (u64) src + n <= (u64) dest || (u64) dest + n <= (u64) src;
    (u64) src <= (u64) src + n;
    (u64) dest <= (u64) dest + n;
    take Src = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Block<unsigned char>(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };
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
    take S = each (u64 i; 0u64 <= i && i < n_start ) { Owned(array_shift(src_start, i)) };
    Src == S;
    take D1 = each (u64 i; n_start - n <= i && i < n_start ) { Block<unsigned char>(array_shift(dest_start, i)) };
    take D2 = each (u64 i; 0u64 <= i && i < n_start - n ) { Owned(array_shift(dest_start, i)) };
    each (u64 i; 0u64 <= i && i < n_start - n ) { S[i] == D2[i] };
  @*/
  {
    /*@ extract Owned<unsigned char>, n_start - n; @*/
    /*@ extract Block<unsigned char>, n_start - n; @*/
    *dest = *src;
    src += 1; dest += 1; n -= 1u;
  }
}
int main()
/*CN_VIP*//*@ accesses x; @*/
{
  int *p = &x;
  int *q;
  /*CN_VIP*/unsigned char *q_bytes = block_int_ptr_to_block_uchar_arr(&q);
  /*CN_VIP*/unsigned char *p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  user_memcpy(q_bytes, p_bytes, sizeof(int *));
  /*CN_VIP*//*@ apply byte_arrays_equal(q_bytes, p_bytes, sizeof<int*>); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(q_bytes); @*/
  /*CN_VIP*//*@ apply byte_ptr_to_int_ptr_ptr(p_bytes); @*/
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*q == 11i32 && *p == 11i32); @*/
}
