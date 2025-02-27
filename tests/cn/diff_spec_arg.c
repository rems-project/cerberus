int foo(int);
/*@ spec foo(i32 y);
requires
    y < MAXi32();
ensures 
    return == y + 1i32;
@*/

int foo(int x)
{
    /*@ assert (x == y); @*/
    x = x + 1;
    /*@ assert (x == y + 1i32); @*/
    return x;
}

int main()
/*@ trusted; @*/
{
    foo(1001);
    return 0;
}
