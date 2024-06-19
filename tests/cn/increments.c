

void
direct (void)
{
  unsigned char x = 1;
  char y = 2;

  x ++;
  y ++;

  y --;
  y --;

}

struct has_short {
  unsigned short x;
};

void
indirect (unsigned char *p, struct has_short *q)
/*@ requires take C = Owned(p); @*/
/*@ requires take S = Owned(q); @*/
/*@ ensures take C2 = Owned(p); @*/
/*@ ensures take S2 = Owned(q); @*/
{
  char x = 1;
  char *r = &x;

  *p++;
  q->x++;
  *r++;
}

int main(void)
/*@ trusted; @*/
{
  struct has_short hs = {.x = 5};
  unsigned char p[1] = {'a'};
  indirect(p, &hs);
}
