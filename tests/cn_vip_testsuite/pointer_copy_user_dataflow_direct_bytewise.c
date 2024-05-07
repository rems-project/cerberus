unsigned char* block_int_ptr_to_block_uchar_arr(int **addr_p)
/*@
trusted;

requires
    take P = Block<int*>(addr_p);

ensures
    return == addr_p;
    take B = Block<unsigned char[sizeof(int*)]>(return);
@*/
{
    return (unsigned char*)addr_p;
}
unsigned char* owned_int_ptr_to_owned_uchar_arr(int **addr_p)
/*@
trusted;

requires
    take P = Owned<int*>(addr_p);

ensures
    return == addr_p;
    take B = Owned<unsigned char[(sizeof(int*))]>(return);
    (u64) P == shift_left((u64)B[7u64], 56u64)
                + shift_left((u64)B[6u64], 48u64)
                + shift_left((u64)B[5u64], 40u64)
                + shift_left((u64)B[4u64], 32u64)
                + shift_left((u64)B[3u64], 24u64)
                + shift_left((u64)B[2u64], 16u64)
                + shift_left((u64)B[1u64], 8u64)
                + (u64)B[0u64];
@*/
{
    return (unsigned char*)addr_p;
}
void byte_ptr_to_int_ptr_ptr(unsigned char *addr_p)
/*@
trusted;

requires
    take B = Owned<unsigned char[(sizeof(int*))]>(addr_p);

ensures
    take P = Owned<int*>(addr_p);
    (u64) P == shift_left((u64)B[7u64], 56u64)
                + shift_left((u64)B[6u64], 48u64)
                + shift_left((u64)B[5u64], 40u64)
                + shift_left((u64)B[4u64], 32u64)
                + shift_left((u64)B[3u64], 24u64)
                + shift_left((u64)B[2u64], 16u64)
                + shift_left((u64)B[1u64], 8u64)
                + (u64)B[0u64];
@*/
{
    return;
}
//CN_VIP #include <stdio.h>
//CN_VIP #include <string.h>
#include <stddef.h>
#include <inttypes.h>
void byte_arrays_equal(unsigned char *x, unsigned char *y, size_t n)
/*@
trusted;

requires
    take X = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(x, i)) };
    take Y = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(y, i)) };
    each (u64 i; 0u64 <= i && i < n) { X[i] == Y[i] };

ensures
    take XR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(x, i)) };
    take YR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(y, i)) };
    X == XR; Y == YR;
    XR == YR;
@*/
{
    return;
}
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
/*@ accesses x; @*/
{
  int *p = &x;
  int *q;
  /*CN_VIP*/if (&p == &q) return 0;                                         // CN used to derive disjointness and non-null
  /*CN_VIP*/if ((uintptr_t)&p + sizeof(int*) < (uintptr_t)&p) return 0;     // constraints from resource ownership, but this
  /*CN_VIP*/if ((uintptr_t)&q + sizeof(int*) < (uintptr_t)&q) return 0;     // was removed for performance reasons.
  /*CN_VIP*/unsigned char *q_bytes = block_int_ptr_to_block_uchar_arr(&q);
  /*CN_VIP*/unsigned char *p_bytes = owned_int_ptr_to_owned_uchar_arr(&p);
  user_memcpy(q_bytes, p_bytes, sizeof(int *));
  /*CN_VIP*/byte_arrays_equal(q_bytes, p_bytes, sizeof(int*));
  /*CN_VIP*/byte_ptr_to_int_ptr_ptr(q_bytes);
  /*CN_VIP*/byte_ptr_to_int_ptr_ptr(p_bytes);
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*q == 11i32 && *p == 11i32); @*/
}
