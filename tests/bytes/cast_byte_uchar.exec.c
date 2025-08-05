[[cerb::byte]] typedef unsigned char byte;

struct foo { int* x; };

int main() 
{
    int x = 0;
    byte *q = (byte*)&x;
    (unsigned char)(q[0]);
    return 0;
}
