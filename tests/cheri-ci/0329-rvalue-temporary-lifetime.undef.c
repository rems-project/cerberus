struct T {
  int a[1];
} st = { 10 };

struct T func(void)
{
  return st;
}

int main(void)
{
  int *p = &func().a[0];
  *p; // UB: the temporary lifetime has already ended
}