int foo(int);
/*@ spec foo(i32 x);
requires
    x < MAXi32();
ensures
    return == x + 1i32;
@*/

int foo(int x)
{
    /*@ assert (x < MAXi32()); @*/
    return x + 1;
}

int main()
/*@ trusted; @*/
{
    foo(100);
    return 0;
}
