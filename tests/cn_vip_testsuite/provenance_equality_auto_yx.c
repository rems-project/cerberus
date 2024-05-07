//CN_VIP #include <stdio.h>
//CN_VIP #include <string.h>
int main() {
  int y=2, x=1;
  int *p = &x + 1;
  int *q = &y;
  //CN_VIP printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  _Bool b = (p==q);
  //CN_VIP printf("(p==q) = %s\n", b?"true":"false");
  /*CN_VIP*//*@ assert (b == 1u8); @*/ // non-det in PNVI-ae-udi; true in VIP
  return 0;
}
