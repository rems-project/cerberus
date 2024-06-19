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


// void *alloc_zeros(long nbytes);
