#include <stddef.h>

[[cerb::byte]] typedef unsigned char byte;

byte *byte_memcpy(byte *dest, byte *src, size_t n) {
    for (int i = 0; i < n; i++)
        dest[i] = src[i];
    return dest;
}

int main() 
{
    int x = 0;
    int y = 1;
    byte_memcpy((byte*)&y, (byte*)&x, sizeof(int));
    return y;
}

