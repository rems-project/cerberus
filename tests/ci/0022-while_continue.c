int main(void) {
  int ret = 0;
  int n = 11;
  while (n > 0) {
    n--;
    if (n % 2 == 0)
      continue;
    ret = ret + n;
    
  }
  return ret; // 25
}
