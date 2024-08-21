/*@
function (boolean) bw_and_precedence() {
    let x = 0i32;
    ~x & 0i32 == 0i32
}
@*/

int main()
{
    /*@ assert (-1i32 & 0i32 == 0i32); @*/
    /*@ assert (bw_and_precedence()); @*/
    int x = 0b110;
    int y = x & 0b101;
    /*@ assert(y == 4i32); @*/
    return 0;
}

