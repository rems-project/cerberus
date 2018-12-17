
#define RTLD_LAZY   __cerbvar_RTLD_LAZY
#define RTLD_NOW    __cerbvar_RTLD_NOW
#define RTLD_GLOBAL __cerbvar_RTLD_GLOBAL
#define RTLD_LOCAL  __cerbvar_RTLD_LOCAL

int    dlclose(void *);
char  *dlerror(void);
void  *dlopen(const char *, int);
void  *dlsym(void *restrict, const char *restrict);

