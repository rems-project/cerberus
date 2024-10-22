void from_bytes(int *p)
/*@ 
requires 
    take X = each (u64 i; i < sizeof<int>) { Block(array_shift<unsigned char>(p, i)) };
ensures
    take Y = Block(p);
@*/
{
    /*@ from_bytes Block(p); @*/
}

void to_bytes(int *p)
/*@ 
requires 
    take Y = Block(p);
ensures
    take X = each (u64 i; i < sizeof<int>) { Block(array_shift<unsigned char>(p, i)) };
@*/
{
    /*@ to_bytes Block(p); @*/
}

int main()
{
    int x = 0;
    int *p = &x;
    to_bytes(p);
    from_bytes(p);
    to_bytes(p);
    from_bytes(p);
}
