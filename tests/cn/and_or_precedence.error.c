// Previously this was binding
// (x == 0i32 && y == 0i32 || x != 0i32) && y != 0i32;
// which made this example pass. Yikes!
void g1(int x, int y)
/*@
requires
    x == 0i32 && y == 0i32 || x != 0i32 && y != 0i32;
ensures
    true;
@*/
{
    if (y != 0) {
        /*@ assert (x != 0i32); @*/
    } else {
        /*@ assert (false); @*/
    }
}
