/*@
function (boolean) bw_compl_expr() {
    let x = 2i32;
    ~(x+x) == -5i32
}
@*/

int main()
{
    /*@ assert (~0i32 == -1i32); @*/
    /*@ assert (bw_compl_expr()); @*/
    int x = 0;
    int y = ~x;
    /*@ assert(y == -1i32); @*/
    return 0;
}
