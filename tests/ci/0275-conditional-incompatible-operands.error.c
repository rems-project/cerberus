void foo() {}
int main()
{
  struct s { int x; } y;
  1 ? y : foo();
}
