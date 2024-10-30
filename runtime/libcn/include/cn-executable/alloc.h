#ifndef CN_ALLOC
#define CN_ALLOC

#ifdef __cplusplus
extern "C" {
#endif

// enum CNTYPE {
//     NODE_CN,
//     SEQ,
//     HASH_TABLE,
//     HT_ENTRY,
//     UNSIGNED_INT,
//     CN_BOOL,
//     CN_POINTER,
//     CNTYPE_SIZE
// };

void *alloc_(long nbytes, const char *, int);

#define alloc(x)\
    alloc_(x, __FILE__, __LINE__)

void *zalloc_(long nbytes, const char *, int);

#define zalloc(x)\
    zalloc_(x, __FILE__, __LINE__)

void free_all(void);

typedef void* alloc_checkpoint;

alloc_checkpoint alloc_save_checkpoint(void);

void free_after(alloc_checkpoint ptr);

// void *alloc_zeros(long nbytes);

#ifdef __cplusplus
}
#endif

#endif // CN_ALLOC
