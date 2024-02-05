int fact(int n) {
  int ret = 1;
  while (n > 0) {
    ret = ret * n;
    n--;
  }
  return ret;
}

int main(void) {
  return fact(5);
}
