int main() {
  int i;
  int *p = &i;
  int j=i;   // is this free of undefined behaviour?
  // note that i is read but the value is not used
}
