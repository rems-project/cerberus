#include <stdio.h>

int *x = NULL;

void f(void)
{
        int y = 1;

        x = &y;
}


int main(void)
{
        f();

        printf("int: %d\n", *x);

        return 0;
}
