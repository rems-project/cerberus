int foo(int);
/*@ spec foo(i32 x);
requires x < MAXi32();
ensures return == x + 1i32; @*/


int foo(int x)
/*@
requires x < MAXi32() - 1i32;
ensures return == x + 2i32; @*/
{
    return x + 2;
}
