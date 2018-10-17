int   x=1, y=2;
int main() {
  int *p = &x + 1;
  int *q = &y;
  *p = 11;  // does this have undefined behaviour?
  return 0;
}
