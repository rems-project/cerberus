#include <stdlib.h>
#include <string.h>

int main()
{
    char *p=malloc(1);
    memcpy(p,p,1);
}
