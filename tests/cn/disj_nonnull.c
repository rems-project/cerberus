int x = 1;
int y = 2;

void globals()
/*@ accesses x; accesses y; @*/
{

  /*@ assert((u64) &x != (u64) &y); @*/

  /*@ assert((u64)&x < (u64)&x + 4u64); @*/
  /*@ assert((u64)&x < MAXu64() - 4u64); @*/

  /*@ assert((u64)&y < MAXu64() - 4u64); @*/
  /*@ assert((u64)&y < (u64)&y + 4u64); @*/

  /*@ assert((u64)&x < (u64)&y || (u64)&x > (u64)&y); @*/
  /*@ assert((u64)&x + 4u64 <= (u64)&y || (u64)&y + 4u64 <= (u64)&x); @*/

}

int main()
{
    int p = 1;
    int q = 2;

  /*@ assert((u64) &p != (u64) &q); @*/

  /*@ assert((u64)&p < (u64)&p + 4u64); @*/
  /*@ assert((u64)&p < MAXu64() - 4u64); @*/

  /*@ assert((u64)&q < MAXu64() - 4u64); @*/
  /*@ assert((u64)&q < (u64)&q + 4u64); @*/

  /*@ assert((u64)&p < (u64)&q || (u64)&p > (u64)&q); @*/
  /*@ assert((u64)&p + 4u64 <= (u64)&q || (u64)&q + 4u64 <= (u64)&p); @*/

}
