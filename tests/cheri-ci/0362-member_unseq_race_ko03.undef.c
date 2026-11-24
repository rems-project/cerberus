// Same as 0360 for the -> operator
struct s { int a; };
int main(void)
{
  struct s arr[2] = {{0}, {1}};
  int i = 0;
  i = (arr + i++)->a; // UB: unsequenced race on i
}
