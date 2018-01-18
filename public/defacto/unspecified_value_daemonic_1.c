int main() {
  int i;
  int *p = &i;
  int j = i;   
  int k = 1/j; // does this have undefined behaviour?
}
