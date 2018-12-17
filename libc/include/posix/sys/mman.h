
#define PROT_EXEC  __cerbvar_PROT_EXEC
#define PROT_NONE  __cerbvar_PROT_NONE
#define PROT_READ  __cerbvar_PROT_READ
#define PROT_WRITE __cerbvar_PROT_WRITE

#define MAP_FIXED   __cerbvar_MAP_FIXED
#define MAP_PRIVATE __cerbvar_MAP_PRIVATE
#define MAP_SHARED  __cerbvar_MAP_SHARED


#define MAP_FAILED __cerbvar_MAP_FAILED


// int    mlock(const void *, size_t);
// int    mlockall(int);
void  *mmap(void *, size_t, int, int, int, off_t);
// int    mprotect(void *, size_t, int);
// int    msync(void *, size_t, int);
// int    munlock(const void *, size_t);
// int    munlockall(void);
int    munmap(void *, size_t);
// int    posix_madvise(void *, size_t, int);
// int    posix_mem_offset(const void *restrict, size_t, off_t *restrict, size_t *restrict, int *restrict);
// int    posix_typed_mem_get_info(int, struct posix_typed_mem_info *);
// int    posix_typed_mem_open(const char *, int, int);
// int    shm_open(const char *, int, mode_t);
// int    shm_unlink(const char *);
