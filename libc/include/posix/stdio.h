#ifndef _POSIX_STDIO_H_
#define _POSIX_STDIO_H_

FILE *fdopen(int, const char *);

int fileno (FILE*);

#define _IONBF __cerbvar__IONBF

#endif
