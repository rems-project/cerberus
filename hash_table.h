/* Credit: https://benhoyt.com/writings/hash-table-in-c/#hash-tables */

// Hash table entry (slot may be filled or empty).
typedef struct {
    unsigned int *key;  // key is NULL if this slot is empty
    void* value;
} ht_entry;

// Hash table structure: create with ht_create, free with ht_destroy.
struct hash_table {
    ht_entry* entries;  // hash slots
    int capacity;    // size of _entries array
    int length;      // number of items in hash table
};

typedef struct hash_table hash_table;

hash_table *create_hash_table(void);

void destroy_hash_table(hash_table *table);

void *ht_get(hash_table *table, unsigned int *key);

unsigned int* ht_set(hash_table* table, unsigned int *key, void* value);

int ht_size(hash_table *table);


typedef struct {
    unsigned int *key;  // current key
    void* value;      // current value

    // Don't use these fields directly.
    hash_table* _table;       // reference to hash table being iterated
    int _index;    // current index into ht._entries
} hash_table_iterator;

hash_table_iterator ht_iterator(hash_table* table);

_Bool ht_next(hash_table_iterator* it);
