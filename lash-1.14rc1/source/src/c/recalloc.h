#ifndef __RECALLOC_H
#define __RECALLOC_H

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

static void* recalloc(void* o, size_t osize, size_t nsize, size_t elemsize) {
  void* n = realloc(o, nsize * elemsize);
  memset(((char*)n + osize  * elemsize), 0, (nsize - osize) * elemsize);
  return n;
}

#endif /* __RECALLOC_H */
