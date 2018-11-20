#include <unistd.h>
#include <stdio.h>
 
int main()
{
    char data[128];
 
    if(read(0, data, 128) < 0)
     write(2, "An error occurred in the read.\n", 31);
    printf("%s\n", data);
 
}
