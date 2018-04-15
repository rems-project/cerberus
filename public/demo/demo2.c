int f(int n) {
  return 20 << n;
}

int g(void){
  int ret = 3;
  int i = 4;
  while (i--) ret--;
  return ret;
}

int main() {
  f(g());
}