

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
/*@ requires take C = RW(p);
             take S = RW(q);
    ensures take C2 = RW(p);
            take S2 = RW(q); @*/
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
