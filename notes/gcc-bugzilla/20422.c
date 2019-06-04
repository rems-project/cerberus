#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define _mymalloc(p,s) mymalloc((void**)(p),(s))

int mymalloc(void **pPointer, size_t size)
{
    *pPointer = malloc(size);

    return (NULL == *pPointer) ? -1 : 0;
}

int main(int argc, char **pArgv)
{
    char *pString;

    // warning: passing arg 1 of `mymalloc' from incompatible pointer type
    // call is GOOD
    if (!mymalloc(&pString, 255)) { free(pString); }

    // warning: passing arg 1 of `mymalloc' from incompatible pointer type
    // call is BAD
    if (!mymalloc(pString, 255)) { free(pString); }

    // call is GOOD, no warning
    if (!_mymalloc(&pString, 255)) { free(pString); }

    // call is BAD, no warning
    if (!_mymalloc(pString, 255)) { free(pString); }

    return 0;
}
