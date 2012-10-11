int f(int *p) {
  return (*p)++;
}

int main(void) {
  int a = 1;
  int *pa = &a;
  return f(pa) % a++;
}
