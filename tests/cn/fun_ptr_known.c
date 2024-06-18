
int
f1 (int x, int y) {
  int z;

  if (x > y) {
    return x - 1;
  }
  else {
    return y;
  }
}

int
f2 (int x, int y) {
  int z;

  z = f1 (x, y);

  return z;
}

typedef int int_binop (int, int);

int_binop *g1 = f2;

int
f3 (int x, int y) {
  int_binop *g2;
  int z;

  g2 = f2;
  z = g2 (x, y);

  return z;
}

int main(void)
{
  int r = f3(1, 2);
}
