// type error

int main(void) {
  const int c = 1;
  int *pc;
  pc = &c;
  return 0;
}
