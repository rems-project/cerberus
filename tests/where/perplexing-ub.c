int main() {
  int *p;
  goto l2;
l1:
  while (1) {
    int x = 5;
    // p = &x;
    return *p;
l2:
    p = &x;
    goto l1;
  }
}
