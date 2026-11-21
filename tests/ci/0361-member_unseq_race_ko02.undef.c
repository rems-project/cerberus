// Same as 0360, when the operand of . is not an lvalue
struct s { int a; };
int main(void)
{
  struct s arr[2] = {{0}, {1}}, t = {2};
  int i = 0;
  i = (arr[i++] = t).a; // UB: unsequenced race on i
}
