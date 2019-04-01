int x=1;
int secret_key = 0123;
int main() {
  int *p = &x;
  p = p+1; {
  int leak = *p;
  return leak; }
}
