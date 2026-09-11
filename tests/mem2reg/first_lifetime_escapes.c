int main()
{

    {
        int x = 4;
        *(&x) = 5;
        goto l2;
l1:
        x = 0;
        return x;
    }
l2:
    goto l1;
}
