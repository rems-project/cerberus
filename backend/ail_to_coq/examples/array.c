struct S {int i; int b[2]; int *c; int (*d)[]; };

int main() {
  struct S nested[1][2];
  struct S a[5];
  struct S b;
  struct S *c;
  struct S (*d)[];
  struct S (*f)[5];
  // note that there is only use, no ! in the generated code (gets
  // canceled by the array decay)
  a[0];
  a[0].i;
  b.i;

  c->i;
  // the following two should generate identical code
  (c + 0)->i;
  (a + 0)->i;

  // the following two should generate identical code
  (*d)[0].i;
  (*f)[0].i;

  a[0].i = 1;
  return 0;
}

// all arguments should have LPtr layout
int test(int a[2], int b[], int *c){
  return 0;
}
