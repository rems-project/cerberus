int y[2], x[2];
int main() {
  int *p = &(x[0]) + (&(y[1])-&(y[0]));
  *p = 11;  // is this free of undefined behaviour?
  return x[1];
}
