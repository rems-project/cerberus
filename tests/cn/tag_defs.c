enum {
  ARRAY_SIZE = 128
};

int f(int *p)
/*@ requires take P = Owned<char[ARRAY_SIZE]>(p) @*/
/*@ ensures take P2 = Owned<char[ARRAY_SIZE]>(p) @*/
{
    return 0;
}
