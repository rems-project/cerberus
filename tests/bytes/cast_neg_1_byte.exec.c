[[cerb::byte]] typedef unsigned char byte;

struct foo { int* x; };

int main()
{
    return (unsigned int)((byte)-1);
}
