struct T {
  int a[1];
} st = { 10 };

struct T func(void)
{
  return st;
}

int printf(const char *, ...);
int main(void)
{
  int *p = &func().a[0];
  printf("%p\n", (void*)p); // when using the zap_dead_pointers switch the value of p should be unspecified
}