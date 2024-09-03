/* One really shouldn't be writing this sort of thing - the correct way to
   write the pre-condition would be:

        has_alloc_id(p);
        // use array_shift(p, _)

   but one might legitimately write and expect to work

        take x = Owned(array_shift(p, 1));

   and so the idiom is supported. */

void array_shift(int *p)
/*@
requires
    has_alloc_id(array_shift(p,-1i64));
ensures
    has_alloc_id(p);
@*/
{
}

struct s {
    char c;
    int x;
};

void member_shift(struct s *p)
/*@
requires
    has_alloc_id(member_shift<s>(p, x));
ensures
    has_alloc_id(p);
@*/
{
}

int main()
{
    int p[2] = {0};
    array_shift(p + 1);

    struct s q = { 0 };
    member_shift(&q);
}
