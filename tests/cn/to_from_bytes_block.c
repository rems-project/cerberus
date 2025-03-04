void from_bytes(int *p)
/*@ 
requires 
    take X = each (u64 i; i < sizeof<int>) { W(array_shift<unsigned char>(p, i)) };
ensures
    take Y = W(p);
@*/
{
    /*@ from_bytes W(p); @*/
}

void to_bytes(int *p)
/*@ 
requires 
    take Y = W(p);
ensures
    take X = each (u64 i; i < sizeof<int>) { W(array_shift<unsigned char>(p, i)) };
@*/
{
    /*@ to_bytes W(p); @*/
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
