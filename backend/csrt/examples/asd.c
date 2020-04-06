int f(int x) {
  x + 1;
}

int g(int x) {
  x * 2;
}

int main(void) {
  int y = f(g(2));
  return 0;
}
