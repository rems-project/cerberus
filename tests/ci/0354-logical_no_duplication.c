// This test is meant to catch regressions in the elaboration that have
// duplicated the evaluation of the operands of && and ||.
// It would also catch a missing sequence point between the left and right
// operands
int main(void)
{
  int x = 0;
  x++ || x++;       // left is 0: right evaluated,     x == 2
  x++ && x++;       // left is 2: right evaluated,     x == 4
  x++ || x++;       // left is 4: right not evaluated, x == 5
  (x++ - 5) && x++; // left is 0: right not evaluated, x == 6
  return x; // returns 6
}
