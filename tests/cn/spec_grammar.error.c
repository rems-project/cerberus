int x;

void f(void)
/*@ accesses x; @*/
{

}

void g(void);
/*@ spec g();
    accesses x;
    cn_function foo;
@*/
