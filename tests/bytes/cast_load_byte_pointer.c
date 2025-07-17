[[cerb::byte]] typedef unsigned char byte;

int main() 
{
    int x = 0;
    byte *p = (byte*)&x;
    int *q = (int*)p;
    byte y = p[0];
    p++;
    return 0;
}
