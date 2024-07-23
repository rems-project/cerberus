unsigned char* int_ptr_ptr_byte_ptr(int **addr_p)
/*@
trusted;

requires
    take P = Owned<int*>(addr_p);

ensures
    ptr_eq(return, addr_p);
    take B = Owned<unsigned char[sizeof(int*)]>(return);
    (u32) P == shift_left((u32)B[3u64], 24u32)
                + shift_left((u32)B[2u64], 16u32)
                + shift_left((u32)B[1u64], 8u32)
                + (u32)B[0u64];
@*/
{
    return (unsigned char*)addr_p;
}

#include <assert.h>
//CN_VIP #include <stdio.h>
#include <stdint.h>
int x=1;
int main()
/*@
accesses
    x;

requires
    bw_and_uf((u32)x, 3u32) == 0u32;
@*/
{
  int *p=&x, *q=&x;
  // read low-order (little endian) representation byte of p
  unsigned char* p_char = int_ptr_ptr_byte_ptr(&p);
  /*@ extract Owned<unsigned char>, 0u64; @*/
  unsigned char i = *p_char;
  // check the bottom two bits of an int* are not usec
  assert(_Alignof(int) >= 4);
  assert((i & 3u) == 0u);
  // set the low-order bit of the byte
  i = i | 1u;
  // write the representation byte back
  *p_char = i;
  // [p might be passed around or copied here]
  // clear the low-order bits again
  *(unsigned char*)&p = (*(unsigned char*)&p) & ~((unsigned char)3u);
  // are p and q now equivalent?
  *p = 11;          // does this have defined behaviour?
  _Bool b = (p==q); // is this true?
  //CN_VIP printf("x=%i *p=%i (p==q)=%s\n",x,*p,b?"true":"false");
  /*CN_VIP*//*@ assert(x == 11i32 && *p == 11i32 && ptr_eq(p, q)); @*/
}
