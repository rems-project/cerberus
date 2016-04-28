int main(void) {
  int i = 0;
  int *pi = &i;
  * ((void *) pi);
  return 0;
}
