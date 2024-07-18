/*  NOTE:
    The second operand must be not equal to zero every time no matter the orientation!
    So the precondition must reflect that. In our case, y and z are on the left hand of the operation.
*/

int nested_mod (int x, int y, int z)
/*@ requires y != 0i32 && z != 0i32;
      let value = (x % y)% z;
    ensures return == value;  @*/
{
    return (x % y) % z;
}