#include <stddef.h>

[[cerb::byte]] typedef unsigned char byte;

byte *byte_memcpy(void *dest, void *src, size_t n) {
    for (int i = 0; i < n; i++)
        ((byte*)dest)[i] = ((byte*)src)[i];
    return dest;
}

int main() 
{
    int x = 0;
    int y = 1;
    byte_memcpy(&y, (byte*)&x, sizeof(int));
    return y;
}

