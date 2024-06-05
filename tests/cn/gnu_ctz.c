int ctz ()
/*@ ensures return == 0i32; @*/
{
  return __builtin_ctz(1);
}

int main(void) {
  int r = ctz();
  return 0;
}