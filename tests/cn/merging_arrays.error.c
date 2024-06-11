void half(int *q) 
/*@ 
requires
    take X = each (u64 i; 5u64 <= i && i < 10u64 ) { Owned(array_shift(q, i)) };
ensures
    take X2 = each (u64 i; 5u64 <= i && i < 10u64 ) { Owned(array_shift(q, i)) };
@*/
{
}

void whole(int *q) 
/*@ 
requires
    take X = each (u64 i; 0u64 <= i && i < 10u64 ) { Owned(array_shift(q, i)) };
ensures
    take X2 = each (u64 i; 0u64 <= i && i < 10u64 ) { Owned(array_shift(q, i)) };
@*/
{
}

int main() 
{
    int a[10] = {0};
    half(a);
    whole(a);
}
