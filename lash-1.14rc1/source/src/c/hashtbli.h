#ifndef __HASHTBLI_H
#define __HASHTBLI_H

#include "recalloc.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>

// Hashtable indexing items by 1-2-3 tuples of integer hashes.
// Stored items must be non are non-null.

struct hashtbli1_elem {
  uint64_t hash1;
  void* data;
};

struct hashtbli2_elem {
  uint64_t hash1, hash2;
  void* data;
};

struct hashtbli3_elem {
  uint64_t hash1, hash2, hash3;
  void* data;
};

struct hashtbli4_elem {
  uint64_t hash1, hash2, hash3, hash4;
  void* data;
};

struct hashtbli5_elem {
  uint64_t hash1, hash2, hash3, hash4, hash5;
  void* data;
};

struct hashtbli1 {
  struct hashtbli1_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

struct hashtbli2 {
  struct hashtbli2_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

struct hashtbli3 {
  struct hashtbli3_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

struct hashtbli4 {
  struct hashtbli4_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

struct hashtbli5 {
  struct hashtbli5_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

static uint32_t hashtbli1_find_index(struct hashtbli1 *h, uint64_t hsh1) {
  uint32_t pos = hsh1 & h->maxelem;
  while (h->d[pos].data && h->d[pos].hash1 != hsh1)
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static uint32_t hashtbli2_find_index(struct hashtbli2 *h, uint64_t hsh1, uint64_t hsh2) {
  uint32_t pos = (hsh1 ^ hsh2) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2))
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static uint32_t hashtbli3_find_index(struct hashtbli3 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3) {
  uint32_t pos = (hsh1 ^ hsh2 ^ hsh3) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2 || h->d[pos].hash3 != hsh3))
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static uint32_t hashtbli4_find_index(struct hashtbli4 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4) {
  uint32_t pos = (hsh1 ^ hsh2 ^ hsh3 ^ hsh4) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2 || h->d[pos].hash3 != hsh3 || h->d[pos].hash4 != hsh4))
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static uint32_t hashtbli5_find_index(struct hashtbli5 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4, uint64_t hsh5) {
  uint32_t pos = (hsh1 ^ hsh2 ^ hsh3 ^ hsh4 ^ hsh5) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2 || h->d[pos].hash3 != hsh3 || h->d[pos].hash4 != hsh4 || h->d[pos].hash5 != hsh5))
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static void* hashtbli1_find(struct hashtbli1 *h, uint64_t hsh1) {
  return (h->d[hashtbli1_find_index(h, hsh1)].data);
}

static void* hashtbli2_find(struct hashtbli2 *h, uint64_t hsh1, uint64_t hsh2) {
  return (h->d[hashtbli2_find_index(h, hsh1, hsh2)].data);
}

static void* hashtbli3_find(struct hashtbli3 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3) {
  return (h->d[hashtbli3_find_index(h, hsh1, hsh2, hsh3)].data);
}

static void* hashtbli4_find(struct hashtbli4 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4) {
  return (h->d[hashtbli4_find_index(h, hsh1, hsh2, hsh3, hsh4)].data);
}

static void* hashtbli5_find(struct hashtbli5 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4, uint64_t hsh5) {
  return (h->d[hashtbli5_find_index(h, hsh1, hsh2, hsh3, hsh4, hsh5)].data);
}

static void hashtbli1_clear(struct hashtbli1 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

static void hashtbli2_clear(struct hashtbli2 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

static void hashtbli3_clear(struct hashtbli3 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

static void hashtbli4_clear(struct hashtbli4 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

static void hashtbli5_clear(struct hashtbli5 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

// Returns: did the rehashing change
static bool hashtbli1_rehash(struct hashtbli1 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli1_find_index(h, hsh1);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static bool hashtbli2_rehash(struct hashtbli2 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1, hsh2 = h->d[i].hash2;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli2_find_index(h, hsh1, hsh2);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->d[pos].hash2 = hsh2;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static bool hashtbli3_rehash(struct hashtbli3 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1, hsh2 = h->d[i].hash2, hsh3 = h->d[i].hash3;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli3_find_index(h, hsh1, hsh2, hsh3);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->d[pos].hash2 = hsh2;
      h->d[pos].hash3 = hsh3;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static bool hashtbli4_rehash(struct hashtbli4 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1, hsh2 = h->d[i].hash2, hsh3 = h->d[i].hash3, hsh4 = h->d[i].hash4;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli4_find_index(h, hsh1, hsh2, hsh3, hsh4);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->d[pos].hash2 = hsh2;
      h->d[pos].hash3 = hsh3;
      h->d[pos].hash4 = hsh4;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static bool hashtbli5_rehash(struct hashtbli5 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1, hsh2 = h->d[i].hash2, hsh3 = h->d[i].hash3, hsh4 = h->d[i].hash4, hsh5 = h->d[i].hash5;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli5_find_index(h, hsh1, hsh2, hsh3, hsh4, hsh5);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->d[pos].hash2 = hsh2;
      h->d[pos].hash3 = hsh3;
      h->d[pos].hash4 = hsh4;
      h->d[pos].hash5 = hsh5;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static void hashtbli1_double(struct hashtbli1 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli1_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { fprintf(stderr, "SZS status Error: hashtbli1_double: Out of memory!\n"); fflush(stderr); exit(137); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli1_rehash(h));
}

static void hashtbli2_double(struct hashtbli2 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli2_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { fprintf(stderr, "SZS status Error: hashtbli2_double: Out of memory!\n"); fflush(stderr); exit(137); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli2_rehash(h));
}

static void hashtbli3_double(struct hashtbli3 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli3_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { fprintf(stderr, "SZS status Error: hashtbli3_double: Out of memory!\n"); fflush(stderr); exit(137); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli3_rehash(h));
}

static void hashtbli4_double(struct hashtbli4 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli4_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { fprintf(stderr, "SZS status Error: hashtbli4_double: Out of memory!\n"); fflush(stderr); exit(137); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli4_rehash(h));
}

static void hashtbli5_double(struct hashtbli5 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli5_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { fprintf(stderr, "SZS status Error: hashtbli5_double: Out of memory!\n"); fflush(stderr); exit(137); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli5_rehash(h));
}

// Returns the pointer to the added item
static void* hashtbli1_add_atpos(struct hashtbli1 *h, uint32_t pos, uint64_t hsh1, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli1_double(h);
  return t;
}

static void* hashtbli2_add_atpos(struct hashtbli2 *h, uint32_t pos, uint64_t hsh1, uint64_t hsh2, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->d[pos].hash2=hsh2;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli2_double(h);
  return t;
}

static void* hashtbli3_add_atpos(struct hashtbli3 *h, uint32_t pos, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->d[pos].hash2=hsh2;
  h->d[pos].hash3=hsh3;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli3_double(h);
  return t;
}

static void* hashtbli4_add_atpos(struct hashtbli4 *h, uint32_t pos, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->d[pos].hash2=hsh2;
  h->d[pos].hash3=hsh3;
  h->d[pos].hash4=hsh4;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli4_double(h);
  return t;
}

static void* hashtbli5_add_atpos(struct hashtbli5 *h, uint32_t pos, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4, uint64_t hsh5, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->d[pos].hash2=hsh2;
  h->d[pos].hash3=hsh3;
  h->d[pos].hash4=hsh4;
  h->d[pos].hash5=hsh5;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli5_double(h);
  return t;
}

static void* hashtbli1_add(struct hashtbli1 *h, uint64_t hsh1, void* t) {
  uint32_t pos = hashtbli1_find_index(h, hsh1);
  return hashtbli1_add_atpos(h, pos, hsh1, t);
}

static void* hashtbli2_add(struct hashtbli2 *h, uint64_t hsh1, uint64_t hsh2, void* t) {
  uint32_t pos = hashtbli2_find_index(h, hsh1, hsh2);
  return hashtbli2_add_atpos(h, pos, hsh1, hsh2, t);
}

static void* hashtbli3_add(struct hashtbli3 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, void* t) {
  uint32_t pos = hashtbli3_find_index(h, hsh1, hsh2, hsh3);
  return hashtbli3_add_atpos(h, pos, hsh1, hsh2, hsh3, t);
}

static void* hashtbli4_add(struct hashtbli4 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4, void* t) {
  uint32_t pos = hashtbli4_find_index(h, hsh1, hsh2, hsh3, hsh4);
  return hashtbli4_add_atpos(h, pos, hsh1, hsh2, hsh3, hsh4, t);
}

static void* hashtbli5_add(struct hashtbli5 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, uint64_t hsh4, uint64_t hsh5, void* t) {
  uint32_t pos = hashtbli5_find_index(h, hsh1, hsh2, hsh3, hsh4, hsh5);
  return hashtbli5_add_atpos(h, pos, hsh1, hsh2, hsh3, hsh4, hsh5, t);
}

static void hashtbli1_make(struct hashtbli1 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli1_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

static void hashtbli2_make(struct hashtbli2 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli2_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

static void hashtbli3_make(struct hashtbli3 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli3_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

static void hashtbli4_make(struct hashtbli4 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli4_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

static void hashtbli5_make(struct hashtbli5 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli5_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

#endif /* __HASHTBLI_H */
