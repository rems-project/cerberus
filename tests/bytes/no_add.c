[[cerb::byte]] typedef unsigned char byte;

int main() 
{
    int x = 0;
    byte *p = (byte*)&x;
    byte y = p[0];
    y + y;
    return 0;
}

