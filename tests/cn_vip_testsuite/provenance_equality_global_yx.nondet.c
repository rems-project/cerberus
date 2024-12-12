//CN_VIP #include <stdio.h>
#include <string.h>
int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses x; requires (u64)&y == (u64)&x + sizeof<int>; @*/
{
  int *p = &x + 1;
  int *q = &y;
  //CN_VIP printf("Addresses: p=%p q=%p\n",(void*)p,(void*)q);
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  //CN_VIP printf("(p==q) = %s\n", b?"true":"false");
#if defined(NON_DET_TRUE)
  /*CN_VIP*//*@ assert (b == 1u8); @*/ // non-det in PNVI-ae-udi; true in VIP
#elif defined(NON_DET_FALSE)
  /*CN_VIP*//*@ assert (b == 0u8); @*/ // non-det in PNVI-ae-udi; true in VIP
#else
  /*CN_VIP*//*@ assert (b == 0u8 || b == 1u8); @*/ // non-det in PNVI-ae-udi; true in VIP
#endif
  return 0;
}
