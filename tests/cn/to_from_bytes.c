int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes Owned(p) ; @*/
    /*@ from_bytes each (u64 i; 0u64 <= i && i < 8u64) { Owned(array_shift(p, i)) }; @*/
    /*@ to_bytes Owned<int>(p) ; @*/
}
