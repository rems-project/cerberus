int main(void) {
  int x;
  if (0) {
    x = 0;
    goto label;
  } else {
    label: x = 1;
  }
  return x;
}
