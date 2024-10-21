int main()
{
    int x = 0;
    int *p = &x;
    char *p_char = (char *)p;
    p_char[2] = 0xff;
}
