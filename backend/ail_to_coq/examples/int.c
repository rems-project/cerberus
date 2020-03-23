int main() {
  int i, j, k;
  long l;
  _Bool b;

  l = 12;

  l = i + j;

  l = l + k;

  b = l == l;

  if (l == l) {
    assert(l == l);
  }

  return 0;
}

long f(int i){
  return i;
}
