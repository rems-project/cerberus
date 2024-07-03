/* Here we test the precedence of the implies operator. Since `and` is stronger than `implies`,
   and `implies` is stronger than `or`, the expression `x == 0i32 && y == 0i32 || x==y implies y!=0i32 && x!=0i32`
   should be parsed as `(x == 0i32 && y == 0i32) || (x==y implies (y!=0i32 && x!=0i32))`,
   and therefore should always be true.
*/

int foo (int x, int y) {
    /*@ assert (x == 0i32 && y == 0i32 || x==y implies y!=0i32 && x!=0i32); @*/
    return 0;
}