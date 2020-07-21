#include <sys/types.h>

// TODO HACK
#define PTHREAD_MUTEX_INITIALIZER 0
#define PTHREAD_MUTEX_RECURSIVE   1

int   pthread_mutex_init(pthread_mutex_t *restrict, const pthread_mutexattr_t *restrict);
int   pthread_mutex_lock(pthread_mutex_t *);
int   pthread_mutex_destroy(pthread_mutex_t *);
int   pthread_mutexattr_destroy(pthread_mutexattr_t *);
int   pthread_mutexattr_init(pthread_mutexattr_t *);
int   pthread_mutexattr_settype(pthread_mutexattr_t *, int);
int   pthread_mutex_trylock(pthread_mutex_t *);
int   pthread_mutex_unlock(pthread_mutex_t *);


int   pthread_create(pthread_t *restrict, const pthread_attr_t *restrict, void *(*)(void*), void *restrict);
int   pthread_join(pthread_t, void **);
