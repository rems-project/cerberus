int main()
{
    void *p;
    int houdini;
escape:
    p = &houdini;
    return p ? 0 : 1;
}
