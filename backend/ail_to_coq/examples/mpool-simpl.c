#define ENTRY_SIZE 4096
#define NULL (void*)0

struct [[rc::size("ENTRY_SIZE"), rc::refined_by("n : {nat}")]] mpool_entry {
    [[rc::field("{n > 0} @ optional<&own<{n - 1} @ mpool_entry>>")]]
    struct mpool_entry *next;
};

struct [[rc::refined_by("n : {nat}")]] mpool {
    [[rc::field("{n > 0} @ optional<&own<{n - 1} @ mpool_entry>>")]]
    struct mpool_entry *entry_list;
};

[[
  rc::args("p @ &own<uninit<{struct_mpool}>>"),
  rc::returns("void"),
  rc::ensures("p @ &own<{0} @ mpool>")
]]
void mpool_init(struct mpool *p) {
    p->entry_list = NULL;
}

[[
  rc::args("p @ &own<{n} @ mpool>"),
  rc::returns("{n > 0} @ optional<&own<uninit<{ENTRY_SIZE}>>>"),
  rc::ensures("p @ &own<{n - 1} @ mpool>")
]]
void *mpool_get(struct mpool *p) {
    if (p->entry_list == NULL) {
        return NULL;
    }
    struct mpool_entry *entry = p->entry_list;
    p->entry_list = entry->next;
    return entry;
}

[[
  rc::args("p @ &own<n @ mpool>", "&own<uninit<{ENTRY_SIZE}>>"),
  rc::returns("void"),
  rc::ensures("p @ &own<{n + 1} @ mpool>")
]]
void mpool_put(struct mpool *p, void *ptr) {
    struct mpool_entry *e = ptr;
    [[rc::subtype("padded<uninit<{struct mpool_entry}>, _, ENTRY_SIZE>")]]
    *e;
    e->next = p->entry_list;
    p->entry_list = e;
}

void* e1, *e2;
int main(void) {
    struct mpool p;
    void * p1, *p2;
    mpool_init(&p);
    mpool_put(&p, &e1);
    mpool_put(&p, &e2);
    p1 = mpool_get(&p);
    assert(p1 != NULL);
    p2 = mpool_get(&p);
    assert(p2 != NULL);
}
