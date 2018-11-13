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
    ht_key (*elem_key)(struct objfs_state *objfs, ht_elem e);
    bool (*equal)(ht_key k1, ht_key k2);
    int (*hash)(ht_key k, int m);
};

struct list {
    ht_elem data;
    struct list* next;
};

void list_free(struct objfs_state *objfs, list p, void (*elem_free)(struct objfs_state *objfs, ht_elem e)) {
    list q;
    while (p != NULL) {
        if (p->data != NULL && elem_free != NULL) {
            (*elem_free)(objfs, p->data);
        }
        q = p->next;
        free(p);
        p = q;
    }
}

chain chain_new();
ht_elem chain_insert(struct objfs_state *objfs, table H, chain C, ht_elem e);
ht_elem chain_search(struct objfs_state *objfs, table H, chain C, ht_key k);
void chain_free(struct objfs_state *objfs, chain C, void (*elem_free)(struct objfs_state *objfs, ht_elem e));

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

list chain_find(struct objfs_state *objfs, table H, chain C, ht_key k) {
    ASSERT(is_chain(C));
    list p = C->list;
    while (p != NULL) {
        if ((*H->equal)(k, (*H->elem_key)(objfs, p->data))) {
            return p;
        }
        p = p->next;
    }
    return NULL;
}

void chain_delete(struct objfs_state *objfs, table H, chain C, ht_elem e, void (*elem_free)(struct objfs_state *objfs, ht_elem e)) {
    ASSERT(is_chain(C));
    list p = C->list;
    list old_p;
    if (p != NULL && p->data == e) {
        C->list = p->next;
        (*elem_free)(objfs, p->data);
        free(p);
        return;
    }
    while (p != NULL && p->data != e) {
        old_p = p;
        p = p->next;
    }
    if (p == NULL) { // Key not present
        return;
    }
    old_p->next = p->next;
    (*elem_free)(objfs, p->data);
    free(p);
}

ht_elem chain_insert(struct objfs_state *objfs, table H, chain C, ht_elem e) {
    ASSERT(is_chain(C) && e != NULL);
    list p = chain_find(objfs, H, C, (*H->elem_key)(objfs, e));
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

ht_elem chain_search(struct objfs_state *objfs, table H, chain C, ht_key k) {
    ASSERT(is_chain(C));
    list p = chain_find(objfs, H, C, k);
    if (p == NULL) {
        return NULL;
    } else {
        return p->data;
    }
}

void chain_free(struct objfs_state *objfs, chain C, void (*elem_free)(struct objfs_state *objfs, ht_elem e)) {
    ASSERT(is_chain(C));
    list_free(objfs, C->list, elem_free);
    free(C);
}

bool is_h_chain (struct objfs_state *objfs, table H, chain C, int h, int m) {
    ASSERT(0 <= h && h < m);
    if (C == NULL) {
        return false;
    }
    list p = C->list;
    while (p != NULL) {
        if (p->data == NULL) {
            return false;
        }
        if ((*H->hash)((*H->elem_key)(objfs, p->data), m) != h) {
            return false;
        }
        p = p->next;
    }
    return true;
}

bool is_table(struct objfs_state *objfs, table H) {
    int i; int m;
    if (H == NULL) {
        return false;
    }
    m = H->size;
    for (i = 0; i < m; i++) {
        chain C = H->array[i];
        if (!(C == NULL || is_h_chain(objfs, H, C, i, m))) {
            return false;
        }
    }
    return true;
}

table table_new(
        struct objfs_state *objfs,
        int init_size,
        ht_key (*elem_key)(struct objfs_state *objfs, ht_elem e),
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
    ASSERT(is_table(objfs, H));
    return H;
}

ht_elem table_search(struct objfs_state *objfs, table H, ht_key k) {
    ASSERT(is_table(objfs, H));
    int h = (*H->hash)(k, H->size);
    if (H->array[h] == NULL) {
        return NULL;
    }
    ht_elem e = chain_search(objfs, H, H->array[h], k);
    ASSERT(e == NULL || (*H->equal)((*H->elem_key)(objfs, e), k));
    return e;
}

ht_elem table_insert(struct objfs_state *objfs, table H, ht_elem e) {
    ASSERT(is_table(objfs, H));
    ht_elem old_e;
    ht_key k = (*H->elem_key)(objfs, e);
    int h = (*H->hash)(k, H->size);
    if (H->array[h] == NULL) {
        H->array[h] = chain_new();
    }
    old_e = chain_insert(objfs, H, H->array[h], e);
    if (old_e != NULL) {
        return old_e;
    }
    H->num_elems++;
    ASSERT(is_table(objfs, H));
    ASSERT(table_search(objfs, H, (*H->elem_key)(objfs, e)) == e);
    return NULL;
}

void table_delete(struct objfs_state *objfs, table H, ht_key k, void (*elem_free)(struct objfs_state *objfs, ht_elem e)) {
    ASSERT(is_table(objfs, H));
    ht_elem e = table_search(objfs, H, k);
    ASSERT(e != NULL);
    int h = (*H->hash)(k, H->size);
    ASSERT(H->array[h] != NULL);
    chain_delete(objfs, H, H->array[h], e, elem_free);
    H->num_elems--;
    ASSERT(is_table(objfs, H));
}

void table_free(struct objfs_state *objfs, table H, void (*elem_free)(struct objfs_state *objfs, ht_elem e)) {
    ASSERT(is_table(objfs, H));
    int i;
    for (i = 0; i < H->size; i++) {
        chain C = H->array[i];
        if (C != NULL) {
            chain_free(objfs, C, elem_free);
        }
    }
    free(H->array);
    free(H);
}
// End Hash Table Implementation
#endif

#ifndef __BITMAP_H__
#define __BITMAP_H__
// This implementation is inspired from here:
// https://github.com/lemire/cbitset

// Start Bitmap Implementation
struct bitmap_t {
    uint64_t* array;
    size_t arraysize;
};
typedef struct bitmap_t* bitmap_t;

bitmap_t bitmap_create(size_t size) {
    bitmap_t bitmap = NULL;
    bitmap = xmalloc(sizeof(struct bitmap_t));
    bitmap->arraysize = (size + sizeof(uint64_t) * 8 - 1) / (sizeof(uint64_t) * 8);
    bitmap->array = xcalloc(bitmap->arraysize, sizeof(uint64_t));
    return bitmap;
}

static inline size_t bitmap_size(const bitmap_t bitmap) {
    return bitmap->arraysize;
}

static inline void bitmap_set_block(bitmap_t bitmap, size_t shiftedi, uint64_t value) {
    bitmap->array[shiftedi] = value;
}

static inline uint64_t bitmap_get_block(const bitmap_t bitmap, size_t shiftedi) {
    return bitmap->array[shiftedi];
}

static inline void bitmap_set(bitmap_t bitmap, size_t i) {
    size_t shiftedi = i >> 6;
    bitmap->array[shiftedi] |= ((uint64_t)1) << (i % 64);
}

static inline void bitmap_clear(bitmap_t bitmap, size_t i) {
    size_t shiftedi = i >> 6;
    bitmap->array[shiftedi] &= (~(((uint64_t)1) << (i % 64)));
}

static inline bool bitmap_get(const bitmap_t bitmap, size_t i) {
    size_t shiftedi = i >> 6;
    if (shiftedi >= bitmap->arraysize) {
        return false;
    }
    return (bitmap->array[shiftedi] & (((uint64_t)1) << (i % 64))) != 0;
}

size_t bitmap_minimum(const bitmap_t bitmap) {
    for (size_t i = 0; i < bitmap->arraysize; i++) {
        uint64_t w = ~(bitmap->array[i]);
        if (w != 0) {
            return __builtin_ctzll(w) + i * 64;
        }
    }
    return 0;
}
// End bitmap Implementation
#endif

#define MAX_OBJS (1024 * 1024) // 2^20 \approx 10^6 objects
#define KEY_LEN (32) // 256 bit keys
#define MAX_BLOCKS (8 * 1024 * 1024) // 32GB / 4KB ==> 8 * 2^20
#define DIR_PTR (12) // 12 direct pointers
#define S_INDIR_PTR (4) // 4 single indirect pointers
#define OBJECT_SIZE (128) // 128 bytes

#define malloc_4k(x) do{\
    (x) = mmap(NULL, BLOCK_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);\
    if ((x) == MAP_FAILED)\
        (x) = NULL;\
} while(0)

#define free_4k(x) munmap((x), BLOCK_SIZE)

typedef struct object* object;
struct object {
    uint32_t id;
    uint32_t size;
    uint32_t cache_index;
    uint32_t cache_dirty;
    char key[KEY_LEN];
    uint32_t dir_ptr[DIR_PTR];
    uint32_t s_indir_ptr[S_INDIR_PTR];
    // Align the object struct to 128 bytes
    uint64_t pad[2];
};

static struct objfs_state *objfs_private;
table objid_table;
bitmap_t block_bitmap;
bitmap_t inode_bitmap;

bool equal(ht_key s1, ht_key s2) {
    for (size_t i = 0; i < KEY_LEN; i++) {
        if (*(((char*)s1) + i) != *(((char*)s2) + i)) {
            return 0;
        }
    }
    return 1;
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

void elem_free(struct objfs_state *objfs, ht_elem e) {
    free(e);
}

static object get_object(struct objfs_state *objfs, uint32_t objid) {
    size_t start_block = (MAX_OBJS + MAX_BLOCKS) / (8 * BLOCK_SIZE);
    size_t inodes_per_block = BLOCK_SIZE / OBJECT_SIZE;
    // objid = x * inodes_per_blocks + y
    size_t x = objid / inodes_per_block;
    size_t y = objid - x * inodes_per_block;

    object objs, obj;
    malloc_4k(objs);
    if (!objs) {
        dprintf("%s: malloc_4k failed\n", __func__);
    }

    if (read_block(objfs, x + start_block, (void*)objs) < 0) {
        dprintf("%s: read_block returned null\n", __func__);
        return NULL;
    }
    if ((objs + y)->id != objid) {
        dprintf("%s: given objid does not matched with the one stored at inode table\n", __func__);
        dprintf("%s: obj->id = %d and objid = %d\n", __func__, (objs + y)->id, objid);
        return NULL;
    }
    obj = malloc(OBJECT_SIZE);
    memcpy(obj, objs + y, OBJECT_SIZE);
    free_4k(objs);
    return obj;
}

ht_key elem_key(struct objfs_state *objfs, ht_elem e) {
    ASSERT(e != NULL);
    return get_object(objfs, *((uint32_t*)e))->key;
}

static int init_bitmap(bitmap_t bitmap, size_t start_block, size_t bitsize, struct objfs_state *objfs) {
    dprintf("%s: start\n", __func__);
    char *ptr;
    malloc_4k(ptr);
    if (!ptr) {
        dprintf("%s: malloc_4k failed\n", __func__);
        return -1;
    }

    bitmap = bitmap_create(bitsize);
    size_t end_block = start_block + bitsize / (8 * BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        if (read_block(objfs, i, ptr) < 0) {
            return -1;
        }
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            bitmap_set_block(bitmap, off + (i - start_block) * BLOCK_SIZE, *((uint64_t*)(ptr + off)));
            off += sizeof(uint64_t);
        }
    }

    free_4k(ptr);
    dprintf("%s: end\n", __func__);
    return 0;
}

static int destroy_bitmap(bitmap_t bitmap, size_t start_block, size_t bitsize, struct objfs_state *objfs) {
    dprintf("%s: start\n", __func__);
    char *ptr;
    malloc_4k(ptr);
    if (!ptr) {
        dprintf("%s: malloc_4k failed\n", __func__);
        return -1;
    }

    ASSERT(bitmap_size(bitmap) == (bitsize + sizeof(uint64_t) * 8 - 1) / (sizeof(uint64_t) * 8));
    size_t end_block = start_block + bitsize / (8 * BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            *((uint64_t*)ptr + off) = bitmap_get_block(bitmap, off + (i - start_block) * BLOCK_SIZE);
            off += sizeof(uint64_t);
        }
        if (write_block(objfs, i, ptr) < 0) {
            return -1;
        }
    }

    free_4k(ptr);
    dprintf("%s: end\n", __func__);
    return 0;
}

static int find_and_read(struct objfs_state *objfs, struct object *obj, char *user_buf, int size) {
    return 0;
}

static int find_and_write(struct objfs_state *objfs, struct object *obj, const char *user_buf, int size) {
    return 0;
}

// Returns the object ID.  -1 (invalid), 0, 1 - reserved
long find_object_id(const char *key, struct objfs_state *objfs) {
    uint32_t objid = *((uint32_t*)table_search(objfs, objid_table, (void*)key));
    object obj = get_object(objfs, objid);
    if (obj->id) {
        ASSERT(equal((void*)(obj->key), (void*)key));
        return obj->id;
    }
    return -1;
}

// Creates a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long create_object(const char *key, struct objfs_state *objfs) {
    // Find a free inode number
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
    if (buf->st_ino < 1) {
        return -1;
    }
    // Had to do this because template for assigment
    // did not provide objfs in this function call
    object obj = get_object(objfs_private, buf->st_ino);
    if (obj->id != buf->st_ino) {
        return -1;
    }
    buf->st_size = obj->size;
    buf->st_blocks = obj->size >> 9;
    if (((obj->size >> 9) << 9) != obj->size) {
        buf->st_blocks += 1;
    }
    return 0;
}

int init_hash_table(struct objfs_state *objfs) {
    object objs;
    malloc_4k(objs);
    if (!objs) {
        dprintf("%s: malloc_4k failed\n", __func__);
    }

    objid_table = table_new(objfs, MAX_OBJS, &elem_key, &equal, &hash);
    size_t start_block = (MAX_OBJS + MAX_BLOCKS) / (8 * BLOCK_SIZE);
    size_t end_block = start_block + (MAX_OBJS * OBJECT_SIZE) / (BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        if (read_block(objfs, i, (void*)objs) < 0) {
            return -1;
        }
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            object obj = objs + off / OBJECT_SIZE;
            if (obj->id == 0) {
                off += OBJECT_SIZE;
                continue;
            }
            uint32_t *id = xmalloc(sizeof(uint32_t));
            *id = obj->id;
            table_insert(objfs, objid_table, id);
            ASSERT(*((uint32_t*)table_search(objfs, objid_table, (void*)obj->key)) == obj->id);
            off += OBJECT_SIZE;
        }
    }

    free_4k(objs);
    return 0;
}

void destroy_hash_table(struct objfs_state *objfs) {
    table_free(objfs, objid_table, &elem_free);
    return;
}

// Set your private pointer, anyway you like.
int objstore_init(struct objfs_state *objfs) {
    objfs_private = objfs;
    if (sizeof(struct object) != OBJECT_SIZE) {
        dprintf("%s: object structure is not of 128 bytes\n", __func__);
        return -1;
    }
    // read the inode bitmap
    if (init_bitmap(inode_bitmap, 0, MAX_OBJS, objfs) < 0) {
        return -1;
    }
    // read the block bitmap
    if (init_bitmap(block_bitmap, MAX_OBJS / (8 * BLOCK_SIZE), MAX_BLOCKS, objfs) < 0) {
        return -1;
    }
    // read the hash table
    if (init_hash_table(objfs) < 0) {
        return -1;
    }
    dprintf("Objstore init completed successfully!\n");
    return 0;
}

// Cleanup private data. FS is being unmounted
int objstore_destroy(struct objfs_state *objfs) {
    // destroy the inode bitmap
    if (destroy_bitmap(inode_bitmap, 0, MAX_OBJS, objfs) < 0) {
        return -1;
    }
    // destroy the block bitmap
    if (destroy_bitmap(block_bitmap, MAX_OBJS / (8 * BLOCK_SIZE), MAX_BLOCKS, objfs) < 0) {
        return -1;
    }
    // destroy the hash table
    destroy_hash_table(objfs);

    dprintf("Objstore destroy completed successfully!\n");
    return 0;
}
