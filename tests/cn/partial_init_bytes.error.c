int main()
{
    int x;
    int *p = &x;
    /*@ to_bytes Block(p); @*/
    char *p_char = (char *)p;
    /*@ extract Block<char>, 2u64; @*/
    p_char[2] = 0xff;
    /*@ from_bytes Owned<int>(p); @*/
}
