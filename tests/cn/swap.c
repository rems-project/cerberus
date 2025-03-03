void swap_pair(unsigned long int *pair)
/*@
requires
   take pairStart = each (i32 j; 0i32 <= j && j < 2i32) {RW(array_shift(pair, j))};
ensures
    take pairEnd = each (i32 j; 0i32 <= j && j < 2i32) {RW(array_shift(pair, j))};
    pairEnd[0i32] == pairStart[1i32];
    pairEnd[1i32] == pairStart[0i32];
@*/
{
    /*@ focus RW<unsigned long int>, 0i32; @*/
    /*@ focus RW<unsigned long int>, 1i32; @*/
    /*@ instantiate good<unsigned long int>, 0i32; @*/
    /*@ instantiate good<unsigned long int>, 1i32; @*/
    unsigned long int tmp = pair[0];
    pair[0] = pair[1];
    pair[1] = tmp;
}

int main(void)
/*@ trusted; @*/
{
  unsigned long int pair[2] = {4, 5};
  swap_pair(pair);
}
