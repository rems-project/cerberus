/*@
lemma check_alloc(pointer p)
requires
    let log = allocs[(alloc_id)p];
    log.base == (u64)p;
    log.size == sizeof<int>;
ensures
    true;
@*/

int main()
{
    int x = 0;
    /*@ apply check_alloc(&x); @*/
    int y = 1;
    /*@ apply check_alloc(&y); @*/
}
