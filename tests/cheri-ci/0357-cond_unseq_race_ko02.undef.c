// Same as 0356, but the selected operand is an integer and the conditional
// has a floating type (the other conversion performed by the elaboration of
// the conditional operator).
int main(void)
{
  int x = 0;
  x = 1 ? x++ : 0.5; // UB: unsequenced race on x
}
