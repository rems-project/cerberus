// https://gcc.gnu.org/bugzilla/attachment.cgi?id=34651&action=edit
#include <stdio.h>
#define __attribute__(a)

typedef int *(*afuncpointer)( void *data );
int *thefunction( void *data __attribute__((unused)))
{
    static int retval = 42;
    return &retval;
}

typedef struct {
    int n;
    struct {
        afuncpointer func;
        void *args;
    } config[10];
} config_t;

int main()
{
    config_t myconfig = {
        .n = 3,
        .config = {
            [0] = { .func = thefunction },
            [1] = { .func = thefunction },
            [3] = { .func = thefunction, .args = &((char*[]){"foo2", "bar2", "baz2"})},
            [4] = { .func = thefunction, .args = &((char*[]){"foo3", "bar3", "baz3"})},
            [3] = { .func = thefunction, .args = &((char*[]){"foo4", "bar4", "baz4"})},
        }
    };

    printf("%s\n", ((char**)myconfig.config[3].args)[0] );
    return 0;
}
