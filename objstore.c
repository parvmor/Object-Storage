#pragma GCC optimize ("O3")
#include "lib.h"
#include "stdbool.h"
#include "pthread.h"

#define malloc_4k(x, ret) do{\
    (x) = mmap(NULL, BLOCK_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);\
    if ((x) == MAP_FAILED) {\
        return (ret);\
    }\
} while(0)

#define xcalloc(x, ret, nobj, size) do {\
    (x) = calloc((nobj), (size));\
    if ((x) == NULL) {\
        return (ret);\
    }\
} while(0)

#define xmalloc(x, ret, size) do {\
    (x) = malloc((size));\
    if ((x) == NULL) {\
        return (ret);\
    }\
} while(0)

#define xfree(x) free((x))
#define free_4k(x) munmap((x), BLOCK_SIZE)
#define KEY_LEN (32) // 256 bit keys
#define MAX_OBJS (1024 * 1024) // 2^20 \approx 10^6 objects
// #define MAX_BLOCKS (8 * 1024 * 1024) // 32GB / 4KB ==> 8 * 2^20
#define MAX_BLOCKS (objfs->disksize)
#define DIR_PTR (12) // 12 direct pointers
#define S_INDIR_PTR (4) // 4 single indirect pointers
#define OBJECT_SIZE (128) // 128 bytes
#define INODES_PER_BLOCK ((BLOCK_SIZE) / (OBJECT_SIZE))
#define INODE_START_BLOCK (((MAX_OBJS) + (MAX_BLOCKS)) / (8 * (BLOCK_SIZE)))
#define DATA_START_BLOCK (INODE_START_BLOCK + (((MAX_OBJS) * (OBJECT_SIZE)) / (BLOCK_SIZE)))
#define MAX_CACHE_BLOCKS ((CACHE_SIZE) / (BLOCK_SIZE))
#define CACHE_MASK ((1<<15) - 1)
#define CACHE_BIT (15)
#define INODE_TABLE_SIZE (DATA_START_BLOCK - INODE_START_BLOCK)

#define min(a, b) (((a) > (b)) ? (b) : (a))
#define max(a, b) (((b) > (a)) ? (b) : (a))

typedef struct objfs_state* objfs_state;
static objfs_state objfs;
volatile int global = 0;

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
    chain* array;
    pthread_mutex_t mutex;
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
    H->array = A;
    H->elem_key = elem_key;
    H->equal = equal;
    H->hash = hash;
    if (pthread_mutex_init(&(H->mutex), NULL) != 0) {
        xfree(H->array);
        xfree(H);
        return NULL;
    }
    return H;
}

int table_lock(table H) {
    if (pthread_mutex_lock(&(H->mutex)) != 0) {
        return -1;
    }
    return 0;
}

int table_unlock(table H) {
    if (pthread_mutex_unlock(&(H->mutex)) != 0) {
        return -1;
    }
    return 0;
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
    return NULL;
}

void table_delete(table H, ht_key k, void (*elem_free)(ht_elem e)) {
    ht_elem e = table_search(H, k);
    int h = (*H->hash)(k, H->size);
    chain_delete(H, H->array[h], e, elem_free);
}

void table_free(table H, void (*elem_free)(ht_elem e)) {
    int i;
    for (i = 0; i < H->size; i++) {
        chain C = H->array[i];
        if (C != NULL) {
            chain_free(C, elem_free);
        }
    }
    if (pthread_mutex_destroy(&(H->mutex)) != 0) {
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
    pthread_mutex_t mutex;
    size_t arraysize;
    size_t prev_free;
};

bitmap_t bitmap_create(size_t size) {
    bitmap_t bitmap;
    xmalloc(bitmap, NULL, sizeof(struct bitmap_t));
    bitmap->arraysize = (size + sizeof(uint64_t) * 8 - 1) / (sizeof(uint64_t) * 8);
    xcalloc(bitmap->array, NULL, bitmap->arraysize, sizeof(uint64_t));
    if (pthread_mutex_init(&(bitmap->mutex), NULL) != 0) {
        return NULL;
    }
    bitmap->prev_free = 0;
    return bitmap;
}

static inline int bitmap_lock(bitmap_t bitmap) {
    if (pthread_mutex_lock(&(bitmap->mutex)) != 0) {
        return -1;
    }
    return 0;
}

static inline int bitmap_unlock(bitmap_t bitmap) {
    if (pthread_mutex_unlock(&(bitmap->mutex)) != 0) {
        return -1;
    }
    return 0;
}

static inline size_t bitmap_size(const bitmap_t bitmap) {
    return bitmap->arraysize;
}

static inline void bitmap_set_block(bitmap_t bitmap, size_t i, uint64_t value) {
    bitmap->array[i >> 6] = value;
}

static inline uint64_t bitmap_get_block(const bitmap_t bitmap, size_t i) {
    return bitmap->array[i >> 6];
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
    if (pthread_mutex_destroy(&(bitmap->mutex)) != 0) {
    }
    free(bitmap->array);
    free(bitmap);
}

size_t bitmap_minimum(const bitmap_t bitmap, int *found) {
    for (size_t i = bitmap->prev_free; i < bitmap->arraysize; i++) {
        uint64_t w = ~(bitmap->array[i]);
        if (w != 0) {
            *found = 1;
            bitmap->prev_free = i;
            return __builtin_ctzll(w) + i * 64;
        }
    }
    for (size_t i = 0; i < bitmap->prev_free; i++) {
        uint64_t w = ~(bitmap->array[i]);
        if (w != 0) {
            *found = 1;
            bitmap->prev_free = i;
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
    char key[KEY_LEN];
    uint32_t dir_ptr[DIR_PTR];
    uint32_t s_indir_ptr[S_INDIR_PTR];
    // Align the object struct to 128 bytes
    uint64_t pad[3];
};

static object get_object(uint32_t objid);
static int set_object(object obj);
static int object_lock(uint32_t objid);
static int object_unlock(uint32_t objid);

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
        if (*(((char*)s1) + i) == 0) {
            return 1;
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
        if (((char*)s)[i] == 0) {
            break;
        }
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
pthread_mutex_t *inode_mutex;

#ifdef CACHE
uint32_t *cache_mapping;
uint32_t *cache_dirty;
pthread_mutex_t *cache_mutex;

static uint32_t cache_hasher(uint32_t a) {
    a = (a + 0x7ed55d16) + (a << 12);
    a = (a ^ 0xc761c23c) ^ (a >> 19);
    a = (a + 0x165667b1) + (a << 5);
    a = (a + 0xd3a2646c) ^ (a << 9);
    a = (a + 0xfd7046c5) + (a << 3);
    a = (a ^ 0xb55a4f09) ^ (a >> 16);
    while (a > CACHE_MASK) {
        a = (a >> CACHE_BIT) + (a & CACHE_MASK);
    }
    return a;
}

static int cache_lock(uint32_t cache_index) {
    if (pthread_mutex_lock(&(cache_mutex[cache_index])) != 0) {
        return -1;
    }
    return 0;
}

static int cache_unlock(uint32_t cache_index) {
    if (pthread_mutex_unlock(&(cache_mutex[cache_index])) != 0) {
        return -1;
    }
    return 0;
}

static int write_dirty_block(uint32_t cache_index, void *buf) {
    if (cache_dirty[cache_index] != 1) {
        return 0;
    }
    if (write_block(objfs, cache_mapping[cache_index], buf) < 0) {
        return -1;
    }
    cache_dirty[cache_index] = 0;
    return 0;
}

static int read_block_cached(uint32_t blockid, void *buf) {
    uint32_t cache_index = cache_hasher(blockid);
    void *cache_ptr = (void*)(objfs->cache + (cache_index << 12));
    cache_lock(cache_index);
    if (cache_mapping[cache_index] != blockid) {
        if (write_dirty_block(cache_index, cache_ptr) < 0) {
            cache_unlock(cache_index);
            return -1;
        }
        cache_mapping[cache_index] = blockid;
        if (read_block(objfs, blockid, cache_ptr) < 0) {
            cache_unlock(cache_index);
            return -1;
        }
    }
    memcpy(buf, cache_ptr, BLOCK_SIZE);
    cache_unlock(cache_index);
    return 0;
}

static int write_block_cached(uint32_t blockid, const void *buf) {
    uint32_t cache_index = cache_hasher(blockid);
    void *cache_ptr = (void*)(objfs->cache + (cache_index << 12));
    cache_lock(cache_index);
    if (cache_mapping[cache_index] != blockid) {
        if (write_dirty_block(cache_index, cache_ptr) < 0) {
            cache_unlock(cache_index);
            return -1;
        }
        cache_mapping[cache_index] = blockid;
        if (read_block(objfs, blockid, cache_ptr) < 0) {
            cache_unlock(cache_index);
            return -1;
        }
    }
    memcpy(cache_ptr, buf, BLOCK_SIZE);
    cache_dirty[cache_index] = 1;
    cache_unlock(cache_index);
    return 0;
}

static int sync_blocks() {
    uint32_t cache_index = 0;
    void *cache_ptr = (void*)(objfs->cache);
    while (cache_index < MAX_CACHE_BLOCKS) {
        if (write_dirty_block(cache_index, cache_ptr) < 0) {
            return -1;
        }
        cache_ptr = cache_ptr + BLOCK_SIZE;
        cache_index += 1;
    }
    return 0;
}
#else
static int read_block_cached(uint32_t blockid, void *buf) {
    if (read_block(objfs, blockid, buf) < 0) {
        return -1;
    }
    return 0;
}

static int write_block_cached(uint32_t blockid, const void *buf) {
    if (write_block(objfs, blockid, (void*)buf) < 0) {
        return -1;
    }
    return 0;
}

static int sync_blocks() {
    return 0;
}
#endif

static int object_lock(uint32_t objid) {
    size_t x = (objid - 2) / INODES_PER_BLOCK;
    if (pthread_mutex_lock(&(inode_mutex[x])) != 0) {
        return -1;
    }
    return 0;
}

static int object_unlock(uint32_t objid) {
    size_t x = (objid - 2) / INODES_PER_BLOCK;
    if (pthread_mutex_unlock(&(inode_mutex[x])) != 0) {
        return -1;
    }
    return 0;
}

static object get_object(uint32_t objid) {
    // objid = x * inodes_per_block + y
    size_t x = (objid - 2) / INODES_PER_BLOCK;
    size_t y = objid - 2 - x * INODES_PER_BLOCK;
    object objs, obj;
    malloc_4k(objs, NULL);
    if (read_block_cached(x + INODE_START_BLOCK, (void*)objs) < 0) {
        free_4k(objs);
        return NULL;
    }
    if ((objs + y)->id != objid) {
        free_4k(objs);
        return NULL;
    }
    xmalloc(obj, NULL, OBJECT_SIZE);
    memcpy((void*)obj, (void*)(objs + y), OBJECT_SIZE);
    free_4k(objs);
    return obj;
}

static int set_object(object obj) {
    // objid = x * inodes_per_block + y
    size_t x = (obj->id - 2) / INODES_PER_BLOCK;
    size_t y = obj->id - 2 - x * INODES_PER_BLOCK;
    object objs;
    malloc_4k(objs, -1);
    if (read_block_cached(x + INODE_START_BLOCK, (void*)objs) < 0) {
        free_4k(objs);
        return -1;
    }
    memcpy((void*)(objs + y), (void*)obj, OBJECT_SIZE);
    if (write_block_cached(x + INODE_START_BLOCK, (void*)objs) < 0) {
        free_4k(objs);
        return -1;
    }
    free_4k(objs);
    return obj->id;
}

static int invalidate_block(uint32_t blockid) {
    if (blockid < DATA_START_BLOCK) {
        return -1;
    }
    bitmap_lock(block_bitmap);
    if (bitmap_get(block_bitmap, blockid - DATA_START_BLOCK) == false) {
        bitmap_unlock(block_bitmap);
        return -1;
    }
    bitmap_unlock(block_bitmap);
#ifdef CACHE
    // remove it from the cache if present
    uint32_t cache_index = cache_hasher(blockid);
    cache_lock(cache_index);
    if (cache_mapping[cache_index] == blockid) {
        cache_mapping[cache_index] = 0;
        cache_dirty[cache_index] = 0;
    }
    cache_unlock(cache_index);
#endif
    bitmap_lock(block_bitmap);
    bitmap_clear(block_bitmap, blockid - DATA_START_BLOCK);
    bitmap_unlock(block_bitmap);
    return 0;
}

static int invalidate_indirect_block(uint32_t blockid) {
    if (blockid < DATA_START_BLOCK) {
        return -1;
    }
    uint32_t *block;
    malloc_4k(block, -1);
    if (read_block_cached(blockid, (void*)block) < 0) {
        return -1;
    }
    for (size_t i = 0; i < BLOCK_SIZE / sizeof(uint32_t); i++) {
        invalidate_block(block[i]);
    }
    free_4k(block);
    invalidate_block(blockid);
    return 0;
}

static int free_object(object obj) {
    uint32_t objid = obj->id;
    obj->id = 0;
    obj->size = 0;
    for (size_t i = 0; i < DIR_PTR; i++) {
        invalidate_block(obj->dir_ptr[i]);
        obj->dir_ptr[i] = 0;
    }
    for (size_t i = 0; i < S_INDIR_PTR; i++) {
        invalidate_indirect_block(obj->s_indir_ptr[i]);
        obj->s_indir_ptr[i] = 0;
    }
    // objid = x * inodes_per_block + y
    size_t x = (objid - 2) / INODES_PER_BLOCK;
    size_t y = objid - 2 - x * INODES_PER_BLOCK;
    object objs;
    malloc_4k(objs, -1);
    if (read_block_cached(x + INODE_START_BLOCK, (void*)objs) < 0) {
        free_4k(objs);
        return -1;
    }
    memcpy((void*)(objs + y), (void*)obj, OBJECT_SIZE);
    if (write_block_cached(x + INODE_START_BLOCK, (void*)objs) < 0) {
        free_4k(objs);
        return -1;
    }
    free_4k(objs);
    return 0;
}

static int write_direct_data_block(object obj, size_t ind, const char *buf, size_t size) {
    int found = 0;
    bitmap_lock(block_bitmap);
    size_t bit_index = bitmap_minimum(block_bitmap, &found);
    if (found == 0) {
        bitmap_unlock(block_bitmap);
        return -1;
    }
    bitmap_set(block_bitmap, bit_index);
    bitmap_unlock(block_bitmap);
    size_t block = bit_index + DATA_START_BLOCK;
    obj->dir_ptr[ind] = block;

    void *ptr;
    malloc_4k(ptr, -1);
    memcpy(ptr, (void*)buf, size);
    if (write_block_cached(block, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }
    free_4k(ptr);
    return 0;
}

static int write_indirect_direct_data_block(object obj, size_t ind, const char *buf, size_t size) {
    size_t indir_ind = (ind - DIR_PTR) / (BLOCK_SIZE / sizeof(uint32_t));
    size_t indir_off = ind - DIR_PTR - indir_ind * (BLOCK_SIZE / sizeof(uint32_t));
    if (indir_ind >= S_INDIR_PTR) {
        return -1;
    }
    if (obj->s_indir_ptr[indir_ind] < DATA_START_BLOCK) {
        int found = 0;
        bitmap_lock(block_bitmap);
        size_t bit_index = bitmap_minimum(block_bitmap, &found);
        if (found == 0) {
            bitmap_unlock(block_bitmap);
            return -1;
        }
        bitmap_set(block_bitmap, bit_index);
        bitmap_unlock(block_bitmap);
        size_t block = bit_index + DATA_START_BLOCK;
        obj->s_indir_ptr[indir_ind] = block;
        void *ptr;
        malloc_4k(ptr, -1);
        for (size_t i = 0; i < BLOCK_SIZE; i++) {
            *((char*)ptr + i) = 0;
        }
        if (write_block_cached(block, ptr) < 0) {
            free_4k(ptr);
            return -1;
        }
        free_4k(ptr);
    }

    size_t blockid = obj->s_indir_ptr[indir_ind];
    uint32_t *ptr;
    malloc_4k(ptr, -1);
    if (read_block_cached(blockid, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }

    int found = 0;
    bitmap_lock(block_bitmap);
    size_t bit_index = bitmap_minimum(block_bitmap, &found);
    if (found == 0) {
        bitmap_unlock(block_bitmap);
        free_4k(ptr);
        return -1;
    }
    bitmap_set(block_bitmap, bit_index);
    bitmap_unlock(block_bitmap);
    size_t block = bit_index + DATA_START_BLOCK;
    ptr[indir_off] = block;
    if (write_block_cached(blockid, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }

    memcpy((void*)ptr, (void*)buf, size);
    if (write_block_cached(block, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }
    free_4k(ptr);
    return 0;
}

static int read_direct_data_block(object obj, size_t ind, const char *buf, size_t size) {
    // Assuming this block is in bitmap
    size_t block = obj->dir_ptr[ind];
    void *ptr;
    malloc_4k(ptr, -1);
    if (read_block_cached(block, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }
    memcpy((void*)buf, ptr, size);
    free_4k(ptr);
    return 0;
}

static int read_indirect_data_block(object obj, size_t ind, const char *buf, size_t size) {
    size_t indir_ind = (ind - DIR_PTR) / (BLOCK_SIZE / sizeof(uint32_t));
    size_t indir_off = ind - DIR_PTR - indir_ind * (BLOCK_SIZE / sizeof(uint32_t));
    if (indir_ind >= S_INDIR_PTR) {
        return -1;
    }
    size_t block = obj->s_indir_ptr[indir_ind];
    uint32_t *ptr;
    malloc_4k(ptr, -1);
    if (read_block_cached(block, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }
    block = ptr[indir_off];
    if (read_block_cached(block, (void*)ptr) < 0) {
        free_4k(ptr);
        return -1;
    }
    memcpy((void*)buf, (void*)ptr, size);
    free_4k(ptr);
    return 0;
}

static int init_bitmap(bitmap_t *bitmap, size_t start_block, size_t bitsize) {
    void *ptr;
    malloc_4k(ptr, -1);
    *bitmap = bitmap_create(bitsize);
    size_t end_block = start_block + bitsize / (8 * BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        if (read_block(objfs, i, ptr) < 0) {
            free_4k(ptr);
            return -1;
        }
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            bitmap_set_block(*bitmap, off + (i - start_block) * BLOCK_SIZE, *((uint64_t*)(ptr + off)));
            off += sizeof(uint64_t);
        }
    }
    free_4k(ptr);
    return 0;
}

static int destroy_bitmap(bitmap_t *bitmap, size_t start_block, size_t bitsize) {
    void *ptr;
    malloc_4k(ptr, -1);
    size_t end_block = start_block + bitsize / (8 * BLOCK_SIZE);
    for (size_t i = start_block; i < end_block; i++) {
        size_t off = 0;
        while (off < BLOCK_SIZE) {
            *((uint64_t*)(ptr + off)) = bitmap_get_block(*bitmap, off + (i - start_block) * BLOCK_SIZE);
            off += sizeof(uint64_t);
        }
        if (write_block(objfs, i, ptr) < 0) {
            free_4k(ptr);
            return -1;
        }
    }
    free_4k(ptr);
    bitmap_free(*bitmap);
    return 0;
}

static int init_hash_table() {
    object objs;
    malloc_4k(objs, -1);
    objid_table = table_new(MAX_OBJS, &elem_key, &equal, &hash);
    for (size_t i = INODE_START_BLOCK; i < DATA_START_BLOCK; i++) {
        if (read_block_cached(i, (void*)objs) < 0) {
            free_4k(objs);
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
    sync_blocks();
    table_free(objid_table, &elem_free);
    return;
}

// Returns the object ID.  -1 (invalid), 0, 1 - reserved
long find_object_id(const char *key, objfs_state objfs_local) {
    while (global == 1);
    objfs = objfs_local;
    table_lock(objid_table);
    void *ptr = table_search(objid_table, (void*)key);
    if (ptr == NULL || *((uint32_t*)ptr) < 2) {
        table_unlock(objid_table);
        return -1;
    }
    uint32_t objid = *((uint32_t*)ptr);
    table_unlock(objid_table);
    return objid;
}

// Creates a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long create_object(const char *key, objfs_state objfs_local) {
    while (global == 1);
    objfs = objfs_local;
    // Check duplicates
    table_lock(objid_table);
    void *ptr = table_search(objid_table, (void*)key);
    if (ptr != NULL) {
        table_unlock(objid_table);
        return -1;
    }
    int found = 0;
    bitmap_lock(inode_bitmap);
    size_t bit_index = bitmap_minimum(inode_bitmap, &found);
    if (found == 0) {
        bitmap_unlock(inode_bitmap);
        table_unlock(objid_table);
        return -1;
    }
    bitmap_set(inode_bitmap, bit_index);
    bitmap_unlock(inode_bitmap);

    object obj;
    xcalloc(obj, -1, 1, sizeof(struct object));
    obj->id = bit_index + 2;
    obj->size = 0;
    for (size_t i = 0; i < DIR_PTR; i++) {
        obj->dir_ptr[i] = 0;
    }
    for (size_t i = 0; i < S_INDIR_PTR; i++) {
        obj->s_indir_ptr[i] = 0;
    }
    memcpy(obj->key, key, KEY_LEN);
    object_lock(obj->id);
    if (set_object(obj) != obj->id) {
        object_unlock(obj->id);
        table_unlock(objid_table);
        free(obj);
        return -1;
    }
    object_unlock(obj->id);

    uint32_t *id;
    xmalloc(id, -1, sizeof(uint32_t));
    *id = obj->id;
    table_insert(objid_table, (void*)key, id);
    table_unlock(objid_table);
    free(obj);
    return bit_index + 2;
}

// One of the users of the object has dropped a reference
// Can be useful to implement caching.
// Return value: Success --> 0
//               Failure --> -1
long release_object(int objid, objfs_state objfs_local) {
    while (global == 1);
    objfs = objfs_local;
    // I don't think this is of any use as of now. Hence, no need to implement it.
    // Maybe useful in cache eviction policies that are not deterministic.
    return 0;
}

// Destroys an object with obj.key=key. Object ID is ensured to be >=2.
// Return value: Success --> 0
//               Failure --> -1
long destroy_object(const char *key, objfs_state objfs_local) {
    while (global == 1);
    objfs = objfs_local;
    table_lock(objid_table);
    void *ptr = table_search(objid_table, (void*)key);
    if (ptr == NULL || *((uint32_t*)ptr) < 2) {
        table_unlock(objid_table);
        return -1;
    }
    uint32_t objid = *((uint32_t*)ptr);
    table_delete(objid_table, (void*)key, &elem_free);
    table_unlock(objid_table);
    object_lock(objid);
    object obj = get_object(objid);
    if (free_object(obj) < 0) {
        object_unlock(objid);
        xfree(obj);
        return -1;
    }
    object_unlock(objid);
    xfree(obj);
    bitmap_lock(inode_bitmap);
    bitmap_clear(inode_bitmap, objid - 2);
    bitmap_unlock(inode_bitmap);
    return 0;
}

// Renames a new object with obj.key=key. Object ID must be >=2.
// Must check for duplicates.
// Return value: Success --> object ID of the newly created object
//               Failure --> -1
long rename_object(const char *key, const char *newname, objfs_state objfs_local) {
    while (global == 1);
    objfs = objfs_local;
    table_lock(objid_table);
    void *ptr = table_search(objid_table, (void*)newname);
    if (ptr != NULL) {
        table_unlock(objid_table);
        return -1;
    }
    ptr = table_search(objid_table, (void*)key);
    if (ptr == NULL || *((uint32_t*)ptr) < 2) {
        table_unlock(objid_table);
        return -1;
    }
    uint32_t objid = *((uint32_t*)ptr);
    table_delete(objid_table, (void*)key, &elem_free);
    uint32_t *id;
    xmalloc(id, -1, sizeof(uint32_t));
    *id = objid;
    table_insert(objid_table, (void*)newname, id);
    table_unlock(objid_table);
    object_lock(objid);
    object obj = get_object(objid);
    memcpy((void*)(obj->key), (void*)newname, KEY_LEN);
    if (set_object(obj) != obj->id) {
        object_unlock(objid);
        free(obj);
        return -1;
    }
    object_unlock(objid);
    free(obj);
    return objid;
}

// Writes the content of the buffer into the object with objid = objid.
// Return value: Success --> #of bytes written
//               Failure --> -1
long objstore_write(int objid, const char *buf, int size, objfs_state objfs_local, off_t offset) {
    while (global == 1);
    objfs = objfs_local;
    if (objid < 2) {
        return -1;
    }
    // offset is 4K aligned.
    if (((offset >> 12) << 12) != offset) {
        return -1;
    }
    object_lock(objid);
    object obj = get_object(objid);
    for (size_t i = 0; i < size; i += BLOCK_SIZE) {
        size_t ind = (i + offset) / BLOCK_SIZE;
        int ret;
        if (ind < DIR_PTR) {
            // Can be written to a direct pointer
            ret = write_direct_data_block(obj, ind, buf + i, min(size - i, BLOCK_SIZE));
        } else {
            // requires an indirect pointer
            ret = write_indirect_direct_data_block(obj, ind, buf + i, min(size - i, BLOCK_SIZE));
        }
        if (ret < 0) {
            object_unlock(objid);
            xfree(obj);
            return -1;
        }
    }
    obj->size += size;
    if (set_object(obj) != obj->id) {
        object_unlock(objid);
        return -1;
    }
    object_unlock(objid);
    dprintf("%d, %s: %d %d %d\n", __LINE__, __func__, obj->id, size, obj->size);
    xfree(obj);
    return size;
}

// Reads the content of the object onto the buffer with objid = objid.
// Return value: Success --> #of bytes read
//               Failure --> -1
long objstore_read(int objid, char *buf, int size, objfs_state objfs_local, off_t offset) {
    while (global == 1);
    objfs = objfs_local;
    if (objid < 2) {
        return -1;
    }
    if (((offset >> 12) << 12) != offset) {
        return -1;
    }
    object obj = get_object(objid);
    for (size_t i = 0; i < size; i += BLOCK_SIZE) {
        size_t ind = (i + offset) / BLOCK_SIZE;
        int ret;
        if (ind < DIR_PTR) {
            ret = read_direct_data_block(obj, ind, buf + i, min(size - i, BLOCK_SIZE));
        } else {
            ret = read_indirect_data_block(obj, ind, buf + i, min(size - i, BLOCK_SIZE));
        }
        if (ret < 0) {
            xfree(obj);
            return -1;
        }
    }
    xfree(obj);
    return size;
}

// Reads the object metadata for obj->id = buf->st_ino
// Fillup buf->st_size and buf->st_blocks correctly
// See man 2 stat
int fillup_size_details(struct stat *buf, objfs_state objfs_local) {
    while (global == 1);
    objfs = objfs_local;
    if (buf->st_ino < 2) {
        return -1;
    }
    object obj = get_object(buf->st_ino);
    if (obj->id != buf->st_ino) {
        xfree(obj);
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
    global = 1;
    if (sizeof(struct object) != OBJECT_SIZE) {
        global = 0;
        return -1;
    }
    if (init_bitmap(&inode_bitmap, 0, MAX_OBJS) < 0) {
        global = 0;
        return -1;
    }
    if (init_bitmap(&block_bitmap, MAX_OBJS / (8 * BLOCK_SIZE), MAX_BLOCKS) < 0) {
        global = 0;
        return -1;
    }
    #ifdef CACHE
    // cache_mapping from MAX_CACHE_BLOCKS to blockid this index represents.
    // block 0 is never hashed and hence is the default value.
    xcalloc(cache_mapping, -1, MAX_CACHE_BLOCKS, sizeof(uint32_t));
    xcalloc(cache_dirty, -1, MAX_CACHE_BLOCKS, sizeof(uint32_t));
    xmalloc(cache_mutex, -1, MAX_CACHE_BLOCKS * sizeof(pthread_mutex_t));
    for (size_t i = 0; i < MAX_CACHE_BLOCKS; i++) {
        if (pthread_mutex_init(&(cache_mutex[i]), NULL) != 0) {
            global = 0;
            return -1;
        }
    }
    #endif
    xmalloc(inode_mutex, -1, INODE_TABLE_SIZE * sizeof(pthread_mutex_t));
    for (size_t i = 0; i < INODE_TABLE_SIZE; i++) {
        if (pthread_mutex_init(&(inode_mutex[i]), NULL) != 0) {
            global = 0;
            return -1;
        }
    }
    if (init_hash_table() < 0) {
        global = 0;
        return -1;
    }
    global = 0;
    dprintf("objstore_init finish\n");
    return 0;
}

// Cleanup private data. FS is being unmounted
int objstore_destroy(objfs_state objfs_local) {
    objfs = objfs_local;
    global = 1;
    if (destroy_bitmap(&inode_bitmap, 0, MAX_OBJS) < 0) {
        global = 0;
        return -1;
    }
    if (destroy_bitmap(&block_bitmap, MAX_OBJS / (8 * BLOCK_SIZE), MAX_BLOCKS) < 0) {
        global = 0;
        return -1;
    }
    destroy_hash_table();
    #ifdef CACHE
    free(cache_mapping);
    free(cache_dirty);
    for (size_t i = 0; i < MAX_CACHE_BLOCKS; i++) {
        if (pthread_mutex_destroy(&(cache_mutex[i])) != 0) {
            global = 0;
            return -1;
        }
    }
    free(cache_mutex);
    #endif
    for (size_t i = 0; i < INODE_TABLE_SIZE; i++) {
        if (pthread_mutex_destroy(&(inode_mutex[i])) != 0) {
            global = 0;
            return -1;
        }
    }
    free(inode_mutex);
    global = 0;
    dprintf("objstore_destroy finish\n");
    return 0;
}
