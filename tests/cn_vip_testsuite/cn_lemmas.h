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

unsigned char* owned_uintptr_t_to_owned_uchar_arr(uintptr_t *addr_p)
/*@
trusted;

requires
    take P = Owned<uintptr_t>(addr_p);

ensures
    return == addr_p;
    take B = Owned<unsigned char[(sizeof(uintptr_t))]>(return);
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
/*@
lemma byte_ptr_to_int_ptr_ptr(pointer addr_p)

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

/*@
lemma byte_ptr_to_uintptr_t(pointer addr_p)

requires
    take B = Owned<unsigned char[(sizeof(uintptr_t))]>(addr_p);

ensures
    take P = Owned<uintptr_t>(addr_p);
    (u64) P == shift_left((u64)B[7u64], 56u64)
                + shift_left((u64)B[6u64], 48u64)
                + shift_left((u64)B[5u64], 40u64)
                + shift_left((u64)B[4u64], 32u64)
                + shift_left((u64)B[3u64], 24u64)
                + shift_left((u64)B[2u64], 16u64)
                + shift_left((u64)B[1u64], 8u64)
                + (u64)B[0u64];
@*/

/*@
lemma byte_arrays_equal(pointer x, pointer y, u64 n)

requires
    take X = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift<unsigned char>(x, i)) };
    take Y = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift<unsigned char>(y, i)) };
    each (u64 i; 0u64 <= i && i < n) { X[i] == Y[i] };

ensures
    take XR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift<unsigned char>(x, i)) };
    take YR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift<unsigned char>(y, i)) };
    X == XR; Y == YR;
    XR == YR;
@*/

int _memcmp(unsigned char *dest, unsigned char *src, size_t n);
/*@ spec _memcmp(pointer dest, pointer src, u64 n);

requires
    (u64) src + n <= (u64) dest || (u64) dest + n <= (u64) src;
    (u64) src <= (u64) src + n;
    (u64) dest <= (u64) dest + n;
    take Src = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };
    Src == SrcR; Dest == DestR;
    (return != 0i32 || Src == Dest) && (return == 0i32 || Src != Dest);
@*/

void _memcpy(unsigned char *dest, unsigned char *src, size_t n);
/*@ spec _memcpy(pointer dest, pointer src, u64 n);

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
    SrcR == DestR;
@*/
