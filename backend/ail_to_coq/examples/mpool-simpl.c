#define ENTRY_SIZE 4096
#define NULL ((void*) 0)

struct mpool_entry {
    /*@ size: ENTRY_SIZE, refined by: n: nat
      next := (n > 0):option<owned_ptr<(n - 1):struct mpool_entry>> */
    struct mpool_entry *next;
};

struct mpool {
    /*@ refined by: n: nat
      entry_list := (n > 0):option<owned_ptr<(n - 1):struct mpool_entry>> */
    struct mpool_entry *entry_list;
};

//@ mpool_init := fn(p:owned_ptr<uninit<struct mpool>>) -> void; p:owned_ptr<0:struct mpool>>
void mpool_init(struct mpool *p) {
    p->entry_list = NULL;
}

/*@ mpool_get := fn(p:owned_ptr<n:struct mpool>) ->
      (n > 0):option<owned_ptr<uninit<ENTRY_SIZE>>>; p:owned_ptr<(max(0, n - 1)):struct mpool>> */
void *mpool_get(struct mpool *p) {
    if (p->entry_list == NULL) {
        return NULL;
    }
    struct mpool_entry *entry = p->entry_list;
    p->entry_list = entry->next;
    return entry;
}

/*@ mpool_put := fn(p:owned_ptr<n:struct mpool>, owned_ptr<uninit<ENTRY_SIZE>>) -> void;
      p:owned_ptr<(n + 1):struct mpool>> */
void mpool_put(struct mpool *p, void *ptr) {
    //@ ptr -> owned_ptr<padded<uninit (struct mpool_entry), _, ENTRY_SIZE>>
    struct mpool_entry *e = ptr;
    e->next = p->entry_list;
    p->entry_list = e;
}

void * e1, * e2;
int main(void) {
    struct mpool p;
    void * p1, * p2;
    mpool_init(&p);
    mpool_put(&p, &e1);
    mpool_put(&p, &e2);
    p1 = mpool_get(&p);
    assert(p1 != NULL);
    p2 = mpool_get(&p);
    assert(p2 != NULL);
}
