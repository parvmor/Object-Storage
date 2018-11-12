#pragma GCC optimize ("O3")
#include "lib.h"
#include "stdbool.h"

#ifdef DBG
#include "assert.h"

#define ASSERT(COND) assert(COND)

#else

#define ASSERT(COND) ((void)0)

#endif

#ifndef __HASH_TABLE_H__
#define __HASH_TABLE_H__
// This implementation is taken from here:
// https://www.cs.cmu.edu/~fp/courses/15122-f10/lectures/22-mem/

// Start Memory Allocation Utilities
void* xcalloc(size_t nobj, size_t size) {
    void* p = calloc(nobj, size);
    if (p == NULL) {
    }
    return p;
}

void* xmalloc(size_t size) {
    void* p = malloc(size);
    if (p == NULL) {
    }
    return p;
}
// End Memory Allocation Utilities

// Start Hash Table Implementation
typedef void* ht_key;
typedef void* ht_elem;
typedef struct table* table;
typedef struct chain* chain;
typedef struct list* list;

struct table {
    int size;
    int num_elems;
    chain* array;
    ht_key (*elem_key)(ht_elem e);
    bool (*equal)(ht_key k1, ht_key k2);
    int (*hash)(ht_key k, int m);
};

struct list {
    ht_elem data;
    struct list* next;
};

void list_free(list p, void (*elem_free)(ht_elem e)) {
    list q;
    while (p != NULL) {
        if (p->data != NULL && elem_free != NULL) {
            (*elem_free)(p->data);
        }
        q = p->next;
        free(p);
        p = q;
    }
}

chain chain_new();
ht_elem chain_insert(table H, chain C, ht_elem e);
ht_elem chain_search(table H, chain C, ht_key k);
void chain_free(chain C, void (*elem_free)(ht_elem e));

struct chain {
    list list;
};

bool is_chain(chain C) {
  return C != NULL;
}

chain chain_new() {
    chain C = xmalloc(sizeof(struct chain));
    C->list = NULL;
    ASSERT(is_chain(C));
    return C;
}

list chain_find(table H, chain C, ht_key k) {
    ASSERT(is_chain(C));
    list p = C->list;
    while (p != NULL) {
        if ((*H->equal)(k, (*H->elem_key)(p->data))) {
            return p;
        }
        p = p->next;
    }
    return NULL;
}

ht_elem chain_insert(table H, chain C, ht_elem e) {
    ASSERT(is_chain(C) && e != NULL);
    list p = chain_find(H, C, (*H->elem_key)(e));
    if (p == NULL) {
        list new_item = xmalloc(sizeof(struct list));
        new_item->data = e;
        new_item->next = C->list;
        C->list = new_item;
        ASSERT(is_chain(C));
        return NULL;
    } else {
        ht_elem old_e = p->data;
        p->data = e;
        ASSERT(is_chain(C));
        return old_e;
    }
}

ht_elem chain_search(table H, chain C, ht_key k) {
    ASSERT(is_chain(C));
    list p = chain_find(H, C, k);
    if (p == NULL) {
        return NULL;
    } else {
        return p->data;
    }
}

void chain_free(chain C, void (*elem_free)(ht_elem e)) {
    ASSERT(is_chain(C));
    list_free(C->list, elem_free);
    free(C);
}

bool is_h_chain (table H, chain C, int h, int m) {
    ASSERT(0 <= h && h < m);
    if (C == NULL) {
        return false;
    }
    list p = C->list;
    while (p != NULL) {
        if (p->data == NULL) {
            return false;
        }
        if ((*H->hash)((*H->elem_key)(p->data), m) != h) {
            return false;
        }
        p = p->next;
    }
    return true;
}

bool is_table(table H) {
    int i; int m;
    if (H == NULL) {
        return false;
    }
    m = H->size;
    for (i = 0; i < m; i++) {
        chain C = H->array[i];
        if (!(C == NULL || is_h_chain(H, C, i, m))) {
            return false;
        }
    }
    return true;
}

table table_new(
        int init_size,
        ht_key (*elem_key)(ht_elem e),
        bool (*equal)(ht_key k1, ht_key k2),
        int (*hash)(ht_key k, int m)) {
    ASSERT(init_size > 1);
    chain* A = xcalloc(init_size, sizeof(chain));
    table H = xmalloc(sizeof(struct table));
    H->size = init_size;
    H->num_elems = 0;
    H->array = A;
    H->elem_key = elem_key;
    H->equal = equal;
    H->hash = hash;
    ASSERT(is_table(H));
    return H;
}

ht_elem table_search(table H, ht_key k) {
    ASSERT(is_table(H));
    int h = (*H->hash)(k, H->size);
    if (H->array[h] == NULL) {
        return NULL;
    }
    ht_elem e = chain_search(H, H->array[h], k);
    ASSERT(e == NULL || (*H->equal)((*H->elem_key)(e), k));
    return e;
}

ht_elem table_insert(table H, ht_elem e) {
    ASSERT(is_table(H));
    ht_elem old_e;
    ht_key k = (*H->elem_key)(e);
    int h = (*H->hash)(k, H->size);
    if (H->array[h] == NULL) {
        H->array[h] = chain_new();
    }
    old_e = chain_insert(H, H->array[h], e);
    if (old_e != NULL) {
        return old_e;
    }
    H->num_elems++;
    ASSERT(is_table(H));
    ASSERT(table_search(H, (*H->elem_key)(e)) == e);
    return NULL;
}

void table_free(table H, void (*elem_free)(ht_elem e)) {
    ASSERT(is_table(H));
    int i;
    for (i = 0; i < H->size; i++) {
        chain C = H->array[i];
        if (C != NULL) chain_free(C, elem_free);
    }
    free(H->array);
    free(H);
}
// End Hash Table Implementation
#endif

#ifndef __BITSET_H__
#define __BITSET_H__
// This implementation is inspired from here:
// https://github.com/lemire/cbitset

// Start Bitset Implementation
struct bitset_t {
    uint64_t* array;
    size_t arraysize;
};
typedef struct bitset_t* bitset_t;

bitset_t bitset_create(size_t size) {
    bitset_t bitset = NULL;
    bitset = xmalloc(sizeof(struct bitset_t));
    bitset->arraysize = (size + sizeof(uint64_t) * 8 - 1) / (sizeof(uint64_t) * 8);
    bitset->array = xcalloc(bitset->arraysize, sizeof(uint64_t));
    return bitset;
}

static inline void bitset_set(bitset_t bitset, size_t i) {
    size_t shiftedi = i >> 6;
    bitset->array[shiftedi] |= ((uint64_t)1) << (i % 64);
}

static inline void bitset_clear(bitset_t bitset, size_t i) {
    size_t shiftedi = i >> 6;
    bitset->array[shiftedi] &= (~(((uint64_t)1) << (i % 64)));
}

static inline bool bitset_get(const bitset_t bitset, size_t i) {
    size_t shiftedi = i >> 6;
    if (shiftedi >= bitset->arraysize) {
        return false;
    }
    return (bitset->array[shiftedi] & (((uint64_t)1) << (i % 64))) != 0;
}

size_t bitset_minimum(const bitset_t bitset) {
    for (size_t i = 0; i < bitset->arraysize; i++) {
        uint64_t w = ~(bitset->array[i]);
        if (w != 0) {
            return __builtin_ctzll(w) + i * 64;
        }
    }
    return 0;
}

// End Bitset Implementation
#endif

#define MAX_OBJS 1000000
#define OBJ_SIZE (16 * 1024 * 1024) // bytes
#define KEY_LEN 32 // bytes

typedef struct object* object;
struct object {
    long id;
    long size;
    char key[KEY_LEN];
};

bool equal(ht_key s1, ht_key s2) {
    return !strcmp((char*)s1, (char*)s2);
}

ht_key elem_key(ht_elem e) {
    ASSERT(e != NULL);
    return ((object)e)->key;
}

int hash(ht_key s, int m) {
    ASSERT(m > 1);
    unsigned int a = 1664525;
    unsigned int b = 1013904223; // Inlined Random Number Generator
    unsigned int r = 0xdeadbeef; // Initial Seed
    int len = KEY_LEN;
    unsigned int h = 0; // An empty string will be mapped to 0.
    for (int i = 0; i < len; i++) {
        h = r * h + ((char*)s)[i]; // mod 2^32
        r = r * a + b; // mod 2^32, linear congruential random number
    }
    h = h % m; // reduce to range
    int hx = (int)h;
    if (hx < 0) {
        hx += m; // Make index positive
    }
    ASSERT(0 <= hx && hx < m);
    return hx;
}

void elem_free(ht_elem e) {
    free(((object)e)->key);
    free(e);
}

object obj;

#define malloc_4k(x) do{\
    (x) = mmap(NULL, BLOCK_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);\
    if ((x) == MAP_FAILED)\
        (x) = NULL;\
} while(0)

#define free_4k(x) munmap((x), BLOCK_SIZE)

static int find_and_read(struct objfs_state *objfs, struct object *obj, char *user_buf, int size) {
    return 0;
}

static int find_and_write(struct objfs_state *objfs, struct object *obj, const char *user_buf, int size) {
    return 0;
}

// Returns the object ID.  -1 (invalid), 0, 1 - reserved
long find_object_id(const char *key, struct objfs_state *objfs) {
    return -1;
}

// Creates a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long create_object(const char *key, struct objfs_state *objfs) {
    return 0;
}

// One of the users of the object has dropped a reference
// Can be useful to implement caching.
// Return value: Success --> 0
//               Failure --> -1
long release_object(int objid, struct objfs_state *objfs) {
    return 0;
}

// Destroys an object with obj.key=key. Object ID is ensured to be >=2.
// Return value: Success --> 0
//               Failure --> -1
long destroy_object(const char *key, struct objfs_state *objfs) {
    return -1;
}

// Renames a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long rename_object(const char *key, const char *newname, struct objfs_state *objfs) {
    return -1;
}

// Writes the content of the buffer into the object with objid = objid.
// Return value: Success --> #of bytes written
//               Failure --> -1
long objstore_write(int objid, const char *buf, int size, off_t offset, struct objfs_state *objfs) {
    return size;
}

// Reads the content of the object onto the buffer with objid = objid.
// Return value: Success --> #of bytes written
//               Failure --> -1
long objstore_read(int objid, char *buf, int size, off_t offset, struct objfs_state *objfs) {
    return size;
}

// Reads the object metadata for obj->id = buf->st_ino
// Fillup buf->st_size and buf->st_blocks correctly
// See man 2 stat
int fillup_size_details(struct stat *buf) {
    return 0;
}

// Set your private pointer, anyway you like.
int objstore_init(struct objfs_state *objfs) {
    return 0;
}

// Cleanup private data. FS is being unmounted
int objstore_destroy(struct objfs_state *objfs) {
    return 0;
}
