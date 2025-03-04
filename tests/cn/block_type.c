// Block does not need to take a CTYPE parameter if it can infer the type from the environment

void block_notype_1(int *p)
/*@ requires take V = W(p);
    ensures  take V2 = W(p);
@*/
{
  ;
}

void block_notype_2(int *p)
/*@ requires take V = W(p);
    ensures  take V2 = RW(p);
@*/
{
  *p = 7;
}