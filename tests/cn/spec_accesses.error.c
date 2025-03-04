int z;

int foo(int);
/*@ spec foo(i32 x);
accesses y;
requires
    x >= 0i32;
    y >= 0i32;
    x < MAXi32() / 2i32;
    y < MAXi32() / 2i32;
ensures
    return == x + y;
@*/

int foo(int x)
{
    return x + z;
}
