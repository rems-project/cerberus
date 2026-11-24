// Same as 0356 for the logical operators (elaborated as conditionals): the
// sequence point of && (§6.5.13#4) and || (§6.5.14#4) is after the first
// operand only, so the side effect of the second operand is unsequenced with
// the store of the assignment.
int main(void)
{
  int x = 1;
  x = 1 && x++; // UB: unsequenced race on x
}
