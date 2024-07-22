int mod_no_parenthesis ()
/*@ ensures return == 10i32; @*/
{
        return 8 + 32 % 5;  // 8 + (32 % 5)
}

int multiply_then_mod ()
/*@ ensures return == 2i32; @*/
{
        return 10 * 14 % 3; // (10 * 14) % 3
}

int divide_multiply_mod_add_subtract ()
/*@ ensures return == 79i32; @*/
{
        return 20 / 10 * 30 - 100 % 2 + 4 * 5 - 10 * 10 / 100; // 2 * 30 - 0 + 20 - 1
}