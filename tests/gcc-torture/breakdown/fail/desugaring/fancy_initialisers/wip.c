union U
{
  struct
  {
    int f1, f2, f3, f4, f5, f6, f7, f8;
    long int f9, f10;
    int f11;
  } f;
  char s[56];
  long int a;
};

union U un = { { 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 } };
