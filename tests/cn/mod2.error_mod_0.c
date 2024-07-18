/* This case will fail since we don't specify that second operand isn't zero.

   Generally every division operation must specify that the second operand must not be zero.
   
   In our case, we must include y != 0i32 since it is the second operand.
   We didn't, so we will expect to see a modulo by zero exception!       */


int mod (int x, int y)
/*@  ensures return == x % y; @*/
{
    return x % y;
}