/*@
lemma byte_arrays_equal(pointer x, pointer y, u64 n)

requires
    take X = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift<unsigned char>(x, i)) };
    take Y = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift<unsigned char>(y, i)) };
    each (u64 i; 0u64 <= i && i < n) { X[i] == Y[i] };

ensures
    take XR = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift<unsigned char>(x, i)) };
    take YR = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift<unsigned char>(y, i)) };
    X == XR; Y == YR;
    XR == YR;
@*/

#include <stddef.h>

int _memcmp(unsigned char *dest, unsigned char *src, size_t n);
/*@ spec _memcmp(pointer dest, pointer src, u64 n);

requires
    (u64) src + n <= (u64) dest || (u64) dest + n <= (u64) src;
    (u64) src <= (u64) src + n;
    (u64) dest <= (u64) dest + n;
    take Src = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { RW(array_shift(dest, i)) };
    Src == SrcR; Dest == DestR;
    (return != 0i32 || Src == Dest) && (return == 0i32 || Src != Dest);
@*/

/*@
lemma assert_equal(u64 x, u64 y)
requires
    true;
ensures
    x == y;
@*/
