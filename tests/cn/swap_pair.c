void swap_pair(unsigned long int *pair_p)
/*@ requires take pairStart = each (integer j; 0 <= j && j < 2) {Owned(pair_p + j)} @*/
/*@ ensures take pairEnd = each (integer j; 0 <= j && j < 2) {Owned(pair_p + j)} @*/
/*@ ensures pairEnd[0] == pairStart[1] @*/
/*@ ensures pairEnd[1] == pairStart[0] @*/
{
    /*@ extract Owned<unsigned long int>, 0; @*/
    unsigned long int tmp = pair_p[0];
    /*@ extract Owned<unsigned long int>, 1; @*/
    /*@ instantiate good<unsigned long int>, 0; @*/
    pair_p[0] = pair_p[1];
    /*@ instantiate good<unsigned long int>, 1; @*/
    pair_p[1] = tmp;
}
