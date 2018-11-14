#pragma GCC optimize ("O3")
#include "lib.h"
#include "stdbool.h"

#define malloc_4k(x, ret) do{\
    (x) = mmap(NULL, BLOCK_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);\
    if ((x) == MAP_FAILED) {\
        dprintf("%s: malloc_4k failed\n", __func__);\
        return (ret);\
    }\
} while(0)

#define xcalloc(x, ret, nobj, size) do {\
    (x) = calloc((nobj), (size));\
    if ((x) == NULL) {\
        dprintf("%s: xcalloc failed with nobj = %d and size = %ld\n", __func__, ((int)(nobj)), (size));\
        return (ret);\
    }\
} while(0)

#define xmalloc(x, ret, size) do {\
    (x) = malloc((size));\
    if ((x) == NULL) {\
        dprintf("%s: xmalloc failed with size = %ld\n", __func__, ((long int)(size)));\
        return (ret);\
    }\
} while(0)

#ifdef CACHE
#define xfree(x) free((x))
#else
#define xfree(x) ((void)0)
#endif

#define free_4k(x) munmap((x), BLOCK_SIZE)
#define KEY_LEN (32) // 256 bit keys
#define MAX_OBJS (1024 * 1024) // 2^20 \approx 10^6 objects
#define MAX_BLOCKS (8 * 1024 * 1024) // 32GB / 4KB ==> 8 * 2^20
#define DIR_PTR (12) // 12 direct pointers
#define S_INDIR_PTR (4) // 4 single indirect pointers
#define OBJECT_SIZE (128) // 128 bytes

typedef struct objfs_state* objfs_state;
static objfs_state objfs;

#ifndef __HASH_TABLE_H__
#define __HASH_TABLE_H__
// This implementation is taken from here:
// https://www.cs.cmu.edu/~fp/courses/15122-f10/lectures/22-mem/

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

struct chain {
    list list;
};

chain chain_new() {
    chain C;
    xmalloc(C, NULL, sizeof(struct chain));
    C->list = NULL;
    return C;
}

list chain_find(table H, chain C, ht_key k) {
    list p = C->list;
    while (p != NULL) {
        ht_key k_prime = (*H->elem_key)(p->data);
        if ((*H->equal)(k, k_prime)) {
            xfree(k_prime);
            return p;
        }
        xfree(k_prime);
        p = p->next;
    }
    return NULL;
}

void chain_delete(table H, chain C, ht_elem e, void (*elem_free)(ht_elem e)) {
    list p = C->list;
    list old_p;
    if (p != NULL && p->data == e) {
        C->list = p->next;
        (*elem_free)(p->data);
        free(p);
        return;
    }
    while (p != NULL && p->data != e) {
        old_p = p;
        p = p->next;
    }
    if (p == NULL) {
        return;
    }
    old_p->next = p->next;
    (*elem_free)(p->data);
    free(p);
}

ht_elem chain_insert(table H, chain C, ht_elem e) {
    ht_key k = (*H->elem_key)(e);
    list p = chain_find(H, C, k);
    xfree(k);
    if (p == NULL) {
        list new_item;
        xmalloc(new_item, NULL, sizeof(struct list));
        new_item->data = e;
        new_item->next = C->list;
        C->list = new_item;
        return NULL;
    } else {
        ht_elem old_e = p->data;
        p->data = e;
        return old_e;
    }
}

ht_elem chain_search(table H, chain C, ht_key k) {
    list p = chain_find(H, C, k);
    if (p == NULL) {
        return NULL;
    } else {
        return p->data;
    }
}

void chain_free(chain C, void (*elem_free)(ht_elem e)) {
    list_free(C->list, elem_free);
    free(C);
}

table table_new(
        int init_size,
        ht_key (*elem_key)(ht_elem e),
        bool (*equal)(ht_key k1, ht_key k2),
        int (*hash)(ht_key k, int m)) {
    chain *A;
    xcalloc(A, NULL, init_size, sizeof(chain));
    table H;
    xmalloc(H, NULL, sizeof(struct table));
    H->size = init_size;
    H->num_elems = 0;
    H->array = A;
    H->elem_key = elem_key;
    H->equal = equal;
    H->hash = hash;
    return H;
}

ht_elem table_search(table H, ht_key k) {
    int h = (*H->hash)(k, H->size);
    if (H->array[h] == NULL) {
        return NULL;
    }
    ht_elem e = chain_search(H, H->array[h], k);
    return e;
}

ht_elem table_insert(table H, ht_key k, ht_elem e) {
    ht_elem old_e;
    int h = (*H->hash)(k, H->size);
    if (H->array[h] == NULL) {
        H->array[h] = chain_new();
    }
    old_e = chain_insert(H, H->array[h], e);
    if (old_e != NULL) {
        return old_e;
    }
    H->num_elems++;
    return NULL;
}

void table_delete(table H, ht_key k, void (*elem_free)(ht_elem e)) {
    ht_elem e = table_search(H, k);
    int h = (*H->hash)(k, H->size);
    chain_delete(H, H->array[h], e, elem_free);
    H->num_elems--;
}

void table_free(table H, void (*elem_free)(ht_elem e)) {
    int i;
    for (i = 0; i < H->size; i++) {
        chain C = H->array[i];
        if (C != NULL) {
            chain_free(C, elem_free);
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
typedef struct bitmap_t* bitmap_t;
struct bitmap_t {
    uint64_t* array;
    size_t arraysize;
};

bitmap_t bitmap_create(size_t size) {
    bitmap_t bitmap;
    xmalloc(bitmap, NULL, sizeof(struct bitmap_t));
    bitmap->arraysize = (size + sizeof(uint64_t) * 8 - 1) / (sizeof(uint64_t) * 8);
    xcalloc(bitmap->array, NULL, bitmap->arraysize, sizeof(uint64_t));
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

void bitmap_free(bitmap_t bitmap) {
    free(bitmap->array);
    free(bitmap);
}

size_t bitmap_minimum(const bitmap_t bitmap, int *found) {
    for (size_t i = 0; i < bitmap->arraysize; i++) {
        uint64_t w = ~(bitmap->array[i]);
        if (w != 0) {
            *found = 1;
            return __builtin_ctzll(w) + i * 64;
        }
    }
    return 0;
}
// End bitmap Implementation
#endif

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

static object get_object(uint32_t objid);
static uint32_t set_object(object obj);

ht_key elem_key(ht_elem e) {
    object obj = get_object(*((uint32_t*)e));
    void *key;
    xcalloc(key, NULL, KEY_LEN, sizeof(char));
    memcpy(key, (void*)(obj->key), KEY_LEN);
    xfree(obj);
    return key;
}

bool equal(ht_key s1, ht_key s2) {
    for (size_t i = 0; i < KEY_LEN; i++) {
        if (*(((char*)s1) + i) != *(((char*)s2) + i)) {
            return 0;
        }
    }
    return 1;
}

int hash(ht_key s, int m) {
    unsigned int a = 1664525;
    unsigned int b = 1013904223; // Inlined Random Number Generator
    unsigned int r = 0xdeadbeef; // Initial Seed
    unsigned int h = 0; // An empty string will be mapped to 0.
    for (int i = 0; i < KEY_LEN; i++) {
        h = r * h + ((char*)s)[i]; // mod 2^32
        r = r * a + b; // mod 2^32, linear congruential random number
    }
    int hx = (int)(h % m);
    if (hx < 0) {
        hx += m;
    }
    return hx;
}

void elem_free(ht_elem e) {
    free(e);
}

table objid_table;
bitmap_t block_bitmap;
bitmap_t inode_bitmap;

static object get_object(uint32_t objid) {
    size_t start_block = (MAX_OBJS + MAX_BLOCKS) / (8 * BLOCK_SIZE);
    size_t inodes_per_block = BLOCK_SIZE / OBJECT_SIZE;
    // objid = x * inodes_per_block + y
    size_t x = (objid - 2) / inodes_per_block;
    size_t y = objid - 2 - x * inodes_per_block;
    object objs, obj;
    malloc_4k(objs, NULL);
    if (read_block(objfs, x + start_block, (void*)objs) < 0) {
        dprintf("%s: read_block returned null\n", __func__);
        return NULL;
    }
    if ((objs + y)->id != objid) {
        dprintf("%s: given objid does not matched with the one stored at inode table\n", __func__);
        dprintf("%s: obj->id = %d and objid = %d\n", __func__, (objs + y)->id, objid);
        return NULL;
    }
    xmalloc(obj, NULL, OBJECT_SIZE);
    memcpy((void*)obj, (void*)(objs + y), OBJECT_SIZE);
    free_4k(objs);
    return obj;
}

static uint32_t set_object(object obj) {
    size_t start_block = (MAX_OBJS + MAX_BLOCKS) / (8 * BLOCK_SIZE);
    size_t inodes_per_block = BLOCK_SIZE / OBJECT_SIZE;
    // objid = x * inodes_per_block + y
    size_t x = (obj->id - 2) / inodes_per_block;
    size_t y = obj->id - 2 - x * inodes_per_block;
    object objs;
    malloc_4k(objs, -1);
    if (read_block(objfs, x + start_block, (void*)objs) < 0) {
        dprintf("%s: read_block returned null\n", __func__);
        return -1;
    }
    memcpy((void*)(objs + y), (void*)obj, OBJECT_SIZE);
    if (write_block(objfs, x + start_block, (void*)objs) < 0) {
        dprintf("%s: write_block returned null\n", __func__);
        return -1;
    }
    free_4k(objs);
    return obj->id;
}

static int init_bitmap(bitmap_t bitmap, size_t start_block, size_t bitsize) {
    void *ptr;
    malloc_4k(ptr, -1);
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
    return 0;
}

static int destroy_bitmap(bitmap_t bitmap, size_t start_block, size_t bitsize) {
    void *ptr;
    malloc_4k(ptr, -1);
    size_t end_block = start_block + bitsize / (8 * BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            *((uint64_t*)(ptr + off)) = bitmap_get_block(bitmap, off + (i - start_block) * BLOCK_SIZE);
            off += sizeof(uint64_t);
        }
        if (write_block(objfs, i, ptr) < 0) {
            return -1;
        }
    }
    free_4k(ptr);
    return 0;
}

static int init_hash_table() {
    object objs;
    malloc_4k(objs, -1);
    objid_table = table_new(MAX_OBJS, &elem_key, &equal, &hash);
    size_t start_block = (MAX_OBJS + MAX_BLOCKS) / (8 * BLOCK_SIZE);
    size_t end_block = start_block + (MAX_OBJS * OBJECT_SIZE) / (BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        if (read_block(objfs, i, (void*)objs) < 0) {
            return -1;
        }
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            object obj = objs + off / OBJECT_SIZE;
            if (obj->id < 2) {
                off += OBJECT_SIZE;
                continue;
            }
            uint32_t *id;
            xmalloc(id, -1, sizeof(uint32_t));
            *id = obj->id;
            table_insert(objid_table, (void*)(obj->key), id);
            off += OBJECT_SIZE;
        }
    }
    free_4k(objs);
    return 0;
}

static void destroy_hash_table() {
    table_free(objid_table, &elem_free);
    return;
}

// Returns the object ID.  -1 (invalid), 0, 1 - reserved
long find_object_id(const char *key, objfs_state objfs_local) {
    objfs = objfs_local;
    void *ptr = table_search(objid_table, (void*)key);
    if (ptr == NULL || *((uint32_t*)ptr) < 2) {
        return -1;
    }
    object obj = get_object(*((uint32_t*)ptr));
    if (!equal((void*)(obj->key), (void*)key)) {
        return -1;
    }
    uint32_t objid = obj->id;
    xfree(obj);
    return objid;
}

// Creates a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long create_object(const char *key, objfs_state objfs_local) {
    objfs = objfs_local;
    // Check duplicates
    void *ptr = table_search(objid_table, (void*)key);
    if (ptr != NULL) {
        return -1;
    }
    // @require: atomicity
    int found = 0;
    size_t bit_index = bitmap_minimum(inode_bitmap, &found);
    if (found == 0) {
        dprintf("%s: objstore is full\n", __func__);
        return -1;
    }
    bitmap_set(inode_bitmap, bit_index);
    // @end: atomicity
    object obj;
    xcalloc(obj, -1, 1, sizeof(struct object));
    obj->id = bit_index + 2;
    #ifdef CACHE
    // do caching init
    #endif
    memcpy(obj->key, key, KEY_LEN);
    if (set_object(obj) != obj->id) {
        xfree(obj);
        return -1;
    }
    xfree(obj);
    return bit_index + 2;
}

// One of the users of the object has dropped a reference
// Can be useful to implement caching.
// Return value: Success --> 0
//               Failure --> -1
long release_object(int objid, objfs_state objfs_local) {
    objfs = objfs_local;
    return 0;
}

// Destroys an object with obj.key=key. Object ID is ensured to be >=2.
// Return value: Success --> 0
//               Failure --> -1
long destroy_object(const char *key, objfs_state objfs_local) {
    objfs = objfs_local;
    void *ptr = table_search(objid_table, (void*)key);
    if (ptr == NULL || *((uint32_t*)ptr) < 2) {
        return -1;
    }

    return -1;
}

// Renames a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long rename_object(const char *key, const char *newname, objfs_state objfs_local) {
    objfs = objfs_local;
    return -1;
}

// Writes the content of the buffer into the object with objid = objid.
// Return value: Success --> #of bytes written
//               Failure --> -1
long objstore_write(int objid, const char *buf, int size, objfs_state objfs_local, off_t offset) {
    objfs = objfs_local;
    return size;
}

// Reads the content of the object onto the buffer with objid = objid.
// Return value: Success --> #of bytes written
//               Failure --> -1
long objstore_read(int objid, char *buf, int size, objfs_state objfs_local, off_t offset) {
    objfs = objfs_local;
    return size;
}

// Reads the object metadata for obj->id = buf->st_ino
// Fillup buf->st_size and buf->st_blocks correctly
// See man 2 stat
int fillup_size_details(struct stat *buf, objfs_state objfs_local) {
    objfs = objfs_local;
    if (buf->st_ino < 2) {
        return -1;
    }
    object obj = get_object(buf->st_ino);
    if (obj->id != buf->st_ino) {
        return -1;
    }
    buf->st_size = obj->size;
    buf->st_blocks = obj->size >> 9;
    if (((obj->size >> 9) << 9) != obj->size) {
        buf->st_blocks += 1;
    }
    xfree(obj);
    return 0;
}

// Set your private pointer, anyway you like.
int objstore_init(objfs_state objfs_local) {
    objfs = objfs_local;
    if (sizeof(struct object) != OBJECT_SIZE) {
        dprintf("%s: object structure is not of 128 bytes\n", __func__);
        return -1;
    }
    if (init_bitmap(inode_bitmap, 0, MAX_OBJS) < 0) {
        return -1;
    }
    if (init_bitmap(block_bitmap, MAX_OBJS / (8 * BLOCK_SIZE), MAX_BLOCKS) < 0) {
        return -1;
    }
    if (init_hash_table() < 0) {
        return -1;
    }
    dprintf("Objstore init completed successfully!\n");
    return 0;
}

// Cleanup private data. FS is being unmounted
int objstore_destroy(objfs_state objfs_local) {
    objfs = objfs_local;
    if (destroy_bitmap(inode_bitmap, 0, MAX_OBJS) < 0) {
        return -1;
    }
    if (destroy_bitmap(block_bitmap, MAX_OBJS / (8 * BLOCK_SIZE), MAX_BLOCKS) < 0) {
        return -1;
    }
    destroy_hash_table();
    dprintf("Objstore destroy completed successfully!\n");
    return 0;
}
