// This is meant to catch an elaboration that strongly sequences the selected
// operand before its conversion to the (integer) result type.
int main(void)
{
  int x = 0;
  x = 1 ? x++ : 0; // UB: unsequenced race on x
}
