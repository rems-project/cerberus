int main()
{ 
    int x = 0;
    goto step1;
step1:
    {
        x =1;
        int y = 1;
        goto step2;
    step2:
        {
            *(&y) = 2;
            int z = 2;
            goto step3;
        step3:
            {
                return x + y + z;
            }
        }
    }
}
