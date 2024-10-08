void swap_pair(unsigned long int *pair_p)
/*@
requires
    take pairStart = each (i32 j; 0i32 <= j && j < 2i32) {Owned(array_shift(pair_p, j))};
ensures
    take pairEnd = each (i32 j; 0i32 <= j && j < 2i32) {Owned(array_shift(pair_p, j))};
    pairEnd[0i32] == pairStart[1i32];
    pairEnd[1i32] == pairStart[0i32];
@*/
{
    /*@ extract Owned<unsigned long int>, 0i32; @*/
    unsigned long int tmp = pair_p[0];
    /*@ extract Owned<unsigned long int>, 1i32; @*/
    /*@ instantiate good<unsigned long int>, 0i32; @*/
    pair_p[0] = pair_p[1];
    /*@ instantiate good<unsigned long int>, 1i32; @*/
    pair_p[1] = tmp;
}

int main(void)
/*@ trusted; @*/
{
  unsigned long int pair_p[2] = {1, 5};
  swap_pair(pair_p);
}
