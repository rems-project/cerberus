struct T {
  int a[1];
} st = { 10 };

struct T func(void)
{
  return st;
}

int main(void)
{
  func().a[0] = 1;
}