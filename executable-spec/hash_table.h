/*

MIT License

Copyright (c) 2021 Ben Hoyt

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

*/

#include "alloc.h"
#include <stdbool.h>

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

hash_table *ht_create(void);

// void destroy_hash_table(hash_table *table);

void *ht_get(hash_table *table, signed long *key);

signed long* ht_set(hash_table* table, signed long *key, void* value);

int ht_size(hash_table *table);


typedef struct {
    signed long *key;  // current key
    void* value;      // current value

    // Dont use these fields directly.
    hash_table* _table;       // reference to hash table being iterated
    int _index;    // current index into ht._entries
} hash_table_iterator;

hash_table_iterator ht_iterator(hash_table* table);

_Bool ht_next(hash_table_iterator* it);
