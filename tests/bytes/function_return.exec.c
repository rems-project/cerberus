[[cerb::byte]] typedef unsigned char byte;

byte f() {
    int x = 0;
    byte *p = (byte*)&x;
    byte y = p[0];
    return y;
}

int main() 
{
    byte b = f();
}
