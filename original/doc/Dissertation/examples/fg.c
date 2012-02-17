int global = 0;

int f(void) {
  return global;
}

int g(void) {
  global += 1;
  return global;
}

int main(void) {
  return f() + g();
}
