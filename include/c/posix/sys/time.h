// int   getitimer(int, struct itimerval *);
int   gettimeofday(struct timeval *restrict, void *restrict);
// int   setitimer(int, const struct itimerval *restrict, struct itimerval *restrict);
// int   select(int, fd_set *restrict, fd_set *restrict, fd_set *restrict, struct timeval *restrict);
int   utimes(const char *, const struct timeval [2]);
