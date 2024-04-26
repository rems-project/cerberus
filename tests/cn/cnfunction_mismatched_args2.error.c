/*@
 function (i32) bw_or(i32 x, i32 y)
 @*/

int c_bw_or(int x, int y, int z)
/*@ cn_function bw_or; @*/
{
    return x | y;
}

