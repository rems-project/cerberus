int f(int *px) {
  return (*px)++;
}

int g(int *px) {
  return (*px)++;;
}

int main(void) {
  int x = 1;
  return f(&x) % g(&x);
}
