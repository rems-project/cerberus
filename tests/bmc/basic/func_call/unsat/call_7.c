int f(int x) {
  return x + 1;
}

int main(void) {
  int x = 1;
  if (x) {
    x = f(x);
  } 

  assert (x == 2);

  return 0;
}
