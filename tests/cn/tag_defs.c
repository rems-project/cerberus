int f(int *p)
/*@ requires take P = Owned<char[4096]>(p) @*/
/*@ ensures take P2 = Owned<char[4096]>(p) @*/
{
    return 0;
}
