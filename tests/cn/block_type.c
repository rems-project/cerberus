void f(int *p)
/*@ requires take V = Block(p);
    ensures  take V2 = Block(p);
@*/
{ 
  ; 
}