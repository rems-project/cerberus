// TODO

// int    chmod(const char *, mode_t);
int    fchmod(int, mode_t);
// int    fchmodat(int, const char *, mode_t, int);
int    fstat(int, struct stat *);
// int    fstatat(int, const char *restrict, struct stat *restrict, int);
// int    futimens(int, const struct timespec [2]);
int    lstat(const char *restrict, struct stat *restrict);
int    mkdir(const char *, mode_t);
// int    mkdirat(int, const char *, mode_t);
// int    mkfifo(const char *, mode_t);
// int    mkfifoat(int, const char *, mode_t);
// int    mknod(const char *, mode_t, dev_t);
// int    mknodat(int, const char *, mode_t, dev_t);
int    stat(const char *restrict, struct stat *restrict);
// mode_t umask(mode_t);
// int    utimensat(int, const char *, const struct timespec [2], int);


// TODO this should be a 1-arg macro
#define S_ISDIR(m) __cerbvar_S_ISDIR(m)
#define S_ISLNK(m) __cerbvar_S_ISLNK(m)
