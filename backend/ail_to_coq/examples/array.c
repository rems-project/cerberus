struct S {int i; int b[2]; int *c;};

int main() {
  struct S a[5];
  struct S b;
  struct S *c;
  a[0];
  a[0].i;
  b.i;
  //(b + 0).i;
  c->i;
  (c + 0)->i;
  (a + 0)->i;
  a[0].i = 1;
  return 0;
}
