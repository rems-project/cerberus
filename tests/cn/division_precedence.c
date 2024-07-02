int divide_no_parenthesis ()
/*@ ensures return == 16i32; @*/
{
        return 8 + 32 / 4;  // 8 + (32 / 4)
}

int multiply_then_divide ()
/*@ ensures return == 28i32; @*/
{
        return 10 * 14 / 5; // (10 * 14) / 5
}

int divide_multiply_add_subtract ()
/*@ ensures return == 29i32; @*/
{
        return 20 / 10 * 30 - 100 / 2 + 4 * 5 - 10 * 10 / 100; // 2 * 30 - 50 + 20 - 1
}
