
void swap_pair(unsigned long int *pair)
/*@ requires take pairStart = each (i32 j; 0i32 <= j && j < 2i32)
    {Owned(array_shift(pair, j))}; @*/
/*@ ensures take pairEnd = each (i32 j; 0i32 <= j && j < 2i32)
    {Owned(array_shift(pair, j))}; @*/
/*@ ensures pairEnd[0i32] == pairStart[1i32]; @*/
/*@ ensures pairEnd[1i32] == pairStart[0i32]; @*/
{
    /*@ extract Owned<unsigned long int>, 0i32; @*/
    /*@ extract Owned<unsigned long int>, 1i32; @*/
    /*@ instantiate good<unsigned long int>, 0i32; @*/
    /*@ instantiate good<unsigned long int>, 1i32; @*/
    unsigned long int tmp = pair[0];
    pair[0] = pair[1];
    pair[1] = tmp;
}

