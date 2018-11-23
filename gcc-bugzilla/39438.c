#include<time.h>
#include<stdio.h>

#define SIZE 256

size_t my_strftime(char *s, size_t max, const char *fmt,
                   const struct tm *tm)
{
    size_t ret;
    ret = strftime(s, max, fmt, tm);
    return ret;
}

int
main ()
{
    char s[SIZE];
    time_t curtime;
    struct tm* loctime;

    curtime = time(NULL);
    loctime = localtime (&curtime);
    my_strftime(s, SIZE, "Hello %A", loctime);
    printf("%s", s);
    return 0;
} 
