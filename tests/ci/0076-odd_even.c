#define true  1
#define false 0


_Bool is_odd(unsigned int n);

_Bool is_even(unsigned int n) {
  if (n == 0)
    return true;
  return is_odd(n-1);
}

_Bool is_odd(unsigned int n) {
  if (n == 0)
    return false;
  return is_even(n-1);
}


int main(void) {
  return 0;
}
