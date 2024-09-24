/*@
function ({i32 x, i32 y}) increment(i32 x, i32 y) {
    {x: x + 1i32, y: y + 1i32}
}

@*/

signed int incr_one(signed int x, signed int y, int flag) 
/*@ requires x < power(2i32, 31i32) - 1i32; 
    requires y < power(2i32, 31i32) - 1i32; @*/
/*@ ensures let pair_record = increment(x, y);
    return == ((flag == 1i32) ? pair_record.x : pair_record.y); @*/
{
    return (flag == 1) ? x + 1 : y + 1;
}


int main(void) 
/*@ trusted; @*/
{
    signed int x = 4;
    signed int y = 2;
    signed int r1 = incr_one(x, y, 1);
    signed int r2 = incr_one(x, y, 0);
    return 0;
}