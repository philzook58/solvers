#include "hashtbli.h"
#include "vector.h"

enum l_kind { NONE=0, DB, NAME, AP, LAM, FAL, IMP, ALL, CHOICE, EQ };

struct tm_struct {
  int16_t tag; int16_t maxv;
  uint16_t x; uint16_t y;
  int32_t no;
  struct tm_struct *l;
  struct tm_struct *r;
  uint64_t id;
  uint64_t size;
  unsigned __int128 fv1;
  unsigned __int128 fv2;
  int64_t lit;
  bool processed;
};
typedef struct tm_struct* trm_p;

#define BLOCK_SIZE (1 << 16)

static struct tm_struct **tm;
static uint32_t x; // position of next tm (or length in current block)
static uint32_t y; // current block number
static uint32_t y_len; // allocated blocks
static uint32_t start_x; // Used by pre-hashed terms not cleared (DBs)

static uint8_t *id; // Hash of all used hashes
static uint32_t idmaxelem;

static struct hashtbli2 aps, lams, imps, alls;
static struct hashtbli3 eqs;

static struct hashtbli3 uhsh, shsh;

static trm_p dbs[256];
static struct vector names, choices;
static trm_p falsep, truep;

static struct vector atom2lit;
static long next_atom = 1;

static struct hashtbli1 tmp_hash;
static bool incomplete = true;

enum t_kind { TNONE=0, TLAM, TALL, TAPR, TAPD, TIMPR, TIMPD, TEQR, TEQD };
struct ftask {
  int16_t ttag;
  trm_p t;
  int32_t no;
  int32_t i;
  int64_t h1, h2;
};

static uint32_t tasks_len;
static struct ftask *tasks;

static void print(trm_p t) {
  switch (t->tag) {
  case DB:
    printf("DB%i", t->no);
    break;
  case NAME:
    printf("NAME%i", t->no);
    break;
  case AP:
    printf("("); print(t->l); printf(" "); print(t->r); printf(")");
    break;
  case LAM:
    printf("(\\:%i.", t->no); print(t->l); printf(")");
    break;
  case FAL:
    printf("FALSE");
    break;
  case IMP:
    if (t->r == falsep) {
      if (t == truep) printf("TRUE");
      else { printf("~ "); print(t->l); }
    } else {
      printf("("); print(t->l); printf(" -> "); print(t->r); printf(")");
    }
    break;
  case ALL:
    printf("(!:%i.", t->no); print(t->l); printf(")");
    break;
  case CHOICE:
    printf("CHOICE%i", t->no);
    break;
  case EQ:
    printf("("); print(t->l); printf(" =%i ", t->no); print(t->r); printf(")");
    break;
  }
}

// TODO check if assignments only if different is faster?
static void double_id() {
  uint32_t newmaxelem = (idmaxelem << 1) + 1;
  id=recalloc(id, idmaxelem + 1, newmaxelem + 1, sizeof(uint8_t));
  for (int i = 0; i <= y; ++i) {
    for (int j = 0; j < ((i == y) ? x : BLOCK_SIZE); ++j) {
      id[tm[i][j].id & idmaxelem]=0;
      id[tm[i][j].id & newmaxelem]=1;
    }
  }
  idmaxelem = newmaxelem;
}

static uint64_t new_id() {
  uint64_t r = rand();
  // make sure hashes are non-zero to allow having them as options
  while (id[r & idmaxelem] || r == 0)
    r = rand();
  id[r & idmaxelem] = 1;
  return r;
}

// Not used
static void tm_id_clear() {
  for (int i = 0; i <= y; ++i) {
    for (int j = ((i == 0) ? start_x : 0); j < ((i == y) ? x : BLOCK_SIZE); ++j) {
      id[tm[i][j].id & idmaxelem]=0;
    }
  }
  y=0; x=start_x;
}

// Finds next position in blocks and returns a cell with x and y set.
static trm_p incr_xy() {
  if (x >= BLOCK_SIZE) {
    x = 0; y++;
    if (y >= y_len) {
      tm[y] = calloc(BLOCK_SIZE, sizeof(struct tm_struct));
      if (!tm[y]) { fprintf(stderr, "SZS status Error: incr_xy: Out of memory!\n"); fflush(stderr); exit(137); }
      y_len++;
    }
    if ((y + 1) * BLOCK_SIZE > (idmaxelem >> 1)) // space for x to grow
      double_id();
  }
  tm[y][x].x=x; tm[y][x].y=y;
  return &tm[y][x++];
}

static trm_p add_tm(int16_t tag, int16_t maxv, int64_t no, trm_p l, trm_p r, uint64_t size, unsigned __int128 fv1, unsigned __int128 fv2) {
  trm_p ret = incr_xy();
  ret->tag = tag; ret->maxv = maxv; ret->no = no; ret->l = l; ret->r = r; ret->id = new_id(); ret->size=size; ret->fv1 = fv1; ret->fv2 = fv2; ret->lit = 0;
  return ret;
}

// vector of task vectors at depths
#define MAX_SUBST_DEPTH 16
struct ftask *stasks[MAX_SUBST_DEPTH];
uint32_t stasks_len[MAX_SUBST_DEPTH];

static void alloc_stasks(int32_t depth) {
  if (depth >= MAX_SUBST_DEPTH) {
    fprintf(stderr, "SZS status Error: alloc_stasks!!!\n");
    fflush(stderr);
    exit(2);
  }
  // printf("Alloc stasks at depth: %i\n", depth);
  stasks_len[depth] = 1 << 20;
  stasks[depth] = calloc(stasks_len[depth], sizeof(struct ftask));
  if (!stasks[depth]) { fprintf(stderr, "SZS status Error: alloc_stasks: Out of memory!\n"); fflush(stderr); exit(137); }

}

static int32_t max32(int32_t a, int32_t b) {
  return ((a) > (b)) ? a : b;
}

static trm_p mk_db(uint32_t vno) {
  if (vno > 255 || vno < 0) {
    fprintf(stderr, "SZS status Error: mk_db called with %i!!!\n", vno);
    fflush(stderr);
    exit(2);
  }
  return dbs[vno];
}

static trm_p mk_name(uint32_t no) {
  while (names.len <= no)
    vector_resize(&names, names.len << 1);
  if (names.data[no]) return names.data[no];
  names.data[no] = add_tm(NAME, 0, no, NULL, NULL, 1, 0, 0);
  return names.data[no];
}

static trm_p mk_ap(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&aps, l->id, r->id);
  if (aps.d[pos].data) return aps.d[pos].data;
  return(hashtbli2_add_atpos(&aps, pos, l->id, r->id,
    add_tm(AP, max32(l->maxv,r->maxv), 0, l, r, l->size+r->size+1, l->fv1 | r->fv1, l->fv2 | r->fv2)));
}

static trm_p mk_lam(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&lams, ((uint64_t)tyno)<<10, t->id);
  if (lams.d[pos].data) return lams.d[pos].data;
  return(hashtbli2_add_atpos(&lams, pos, ((uint64_t)tyno)<<10, t->id,
    add_tm(LAM, max32(0,t->maxv-1), tyno, t, NULL, t->size+1, t->fv1>>1, (t->fv2>>1) | ((t->fv1 & 1) << 127))));
}

static trm_p mk_false() {
  return falsep;
}

static trm_p mk_imp(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&imps, l->id, r->id);
  if (imps.d[pos].data) return imps.d[pos].data;
  return(hashtbli2_add_atpos(&imps, pos, l->id, r->id,
    add_tm(IMP, max32(l->maxv,r->maxv), 0, l, r, l->size+r->size+1,l->fv1 | r->fv1, l->fv2 | r->fv2)));
}

static trm_p mk_norm_imp(trm_p l, trm_p r) {
  if (incomplete && (r == falsep && l->tag == IMP && l->r == falsep)) return l->l; // double negation
  if (incomplete && (r == truep || l == falsep || l == r)) return truep;
  if (incomplete && l == truep) return r;
  return mk_imp(l, r);
}

static trm_p mk_all(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&alls, ((uint64_t)tyno)<<10, t->id);
  if (alls.d[pos].data) return alls.d[pos].data;
  return(hashtbli2_add_atpos(&alls, pos, ((uint64_t)tyno)<<10, t->id,
    add_tm(ALL, max32(0,t->maxv-1), tyno, t, NULL, t->size+1, t->fv1>>1, (t->fv2>>1) | ((t->fv1 & 1) << 127))));
}

static trm_p mk_choice(uint32_t no) {
  while (choices.len <= no)
    vector_resize(&choices, choices.len << 1);
  if (choices.data[no]) return choices.data[no];
  choices.data[no] = add_tm(CHOICE, 0, no, NULL, NULL, 1, 0, 0);
  return choices.data[no];
}

static trm_p mk_eq(uint32_t tyno, trm_p l, trm_p r) {
  uint32_t pos = hashtbli3_find_index(&eqs, ((uint64_t)tyno)<<10, l->id, r->id);
  if (eqs.d[pos].data) return eqs.d[pos].data;
  return(hashtbli3_add_atpos(&eqs, pos, ((uint64_t)tyno)<<10, l->id, r->id,
    add_tm(EQ, max32(l->maxv,r->maxv), tyno, l, r, l->size+r->size+1, l->fv1 | r->fv1, l->fv2 | r->fv2)));
}

static trm_p mk_norm_eq(uint32_t tyno, trm_p l, trm_p r) {
  if (incomplete && l == falsep) return mk_norm_imp(r, falsep);
  if (incomplete && r == falsep) return mk_norm_imp(l, falsep);
  if (incomplete && l == r) return truep;
  return mk_eq(tyno, l, r);
}

void add_task6(struct ftask* tsk, int16_t tag, trm_p t, int32_t no, int32_t i, int64_t h1, int64_t h2) {
  tsk->ttag=tag; tsk->no=no; tsk->t=t; tsk->i=i; tsk->h1=h1; tsk->h2=h2;
}

void add_task5(struct ftask* tsk, int16_t tag, trm_p t, int32_t i, int64_t h1, int64_t h2) {
  tsk->ttag=tag; tsk->t=t; tsk->i=i; tsk->h1=h1; tsk->h2=h2;
}

void add_task4(struct ftask* tsk, int16_t tag, int32_t no, int64_t h1, int64_t h2) {
  tsk->ttag=tag; tsk->no=no; tsk->h1=h1; tsk->h2=h2;
}

#ifdef CACHE_SUBST
#define SAVE_SUBST(a,b,c,d,e) { hashtbli3_add(a,b,c,d,e);}
#else
#define SAVE_SUBST(a,b,c,d,e) ;
#endif

static trm_p uptrm_tt(trm_p t, int32_t i, int32_t j) {
  bool istm=true; int32_t tl=0; trm_p t2;
  while (true) {
    if (istm) {
      if (t->maxv <= i) {istm = false; continue; }
#ifdef CACHE_SUBST
      t2 = hashtbli3_find (&uhsh, t->id, i << 10, j << 20);
      if (t2) {istm = false; t = t2; continue; }
#endif
      if (tl >= tasks_len) {
        printf ("Extendings u-tasks to: %li MB\n", (tasks_len * sizeof(struct ftask)) >> 19);
        tasks=recalloc(tasks, tasks_len, tasks_len << 1, sizeof(struct ftask));
        if (!tasks) { fprintf(stderr, "SZS status Error: uptrm_tt: Out of memory!\n"); fflush(stderr); exit(137); }
        tasks_len = tasks_len << 1;
      }
      switch (t->tag) {
        case AP:  add_task5(&tasks[tl], TAPR,  t->r, i, t->id, i << 10); t=t->l; tl++; continue;
        case IMP: add_task5(&tasks[tl], TIMPR, t->r, i, t->id, i << 10); t=t->l; tl++; continue;
        case EQ:  add_task6(&tasks[tl], TEQR,  t->r, t->no, i, t->id, i << 10); t=t->l; tl++; continue;
        case DB: istm = false; if (t->no >= i) t = mk_db(t->no+j); continue;
        case ALL: add_task4(&tasks[tl], TALL, t->no, t->id, i << 10); t=t->l; i++; tl++; continue;
        case LAM: add_task4(&tasks[tl], TLAM, t->no, t->id, i << 10); t=t->l; i++; tl++; continue;
        default: istm = false;
      }
    } else {
      if (tl <= 0) return t;
      tl--;
      switch (tasks[tl].ttag) {
        case TAPR: istm=true; t2=t; t=tasks[tl].t; i=tasks[tl].i; tasks[tl].ttag=TAPD; tasks[tl].t=t2; tl++; continue;
        case TAPD: t=mk_ap(tasks[tl].t, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        case TIMPR: istm=true; t2=t; t=tasks[tl].t; i=tasks[tl].i; tasks[tl].ttag=TIMPD; tasks[tl].t=t2; tl++; continue;
        case TIMPD: t=mk_imp(tasks[tl].t, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        case TEQR: istm=true; t2=t; t=tasks[tl].t; i=tasks[tl].i; tasks[tl].ttag=TEQD; tasks[tl].t=t2; tl++; continue;
        case TEQD: t=mk_eq(tasks[tl].no, tasks[tl].t, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        case TALL: t=mk_all(tasks[tl].no, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        case TLAM: t=mk_lam(tasks[tl].no, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        default: fprintf(stderr, "SZS status Error: uptrm_tt: TNONE @ %i : %i\n", tl, tasks[tl].ttag); exit(2);
      }
    }
  }
}

static trm_p uptrm(trm_p t, int32_t i, int32_t j) {
  if (j == 0) return t;
  return uptrm_tt(t, i, j);
}

/* Recursive version. Allocates stack and does no caching.
static trm_p uptrm(trm_p t, int32_t i, int32_t j) {
  if (t->maxv <= i)
    return t;
  switch (t->tag) {
  case DB:
    {const int32_t k = t->no;
    return mk_db( (k < i) ? k : k + j);}
  case AP:
    return mk_ap(uptrm(t->l, i, j), uptrm(t->r, i, j));
  case LAM:
    return mk_lam(t->no, uptrm(t->l, (i + 1), j));
  case IMP:
    return mk_imp(uptrm(t->l, i, j), uptrm(t->r, i, j));
  case ALL:
    return mk_all(t->no, uptrm(t->l, (i + 1), j));
  case EQ:
    return mk_eq(t->no, uptrm(t->l, i, j), uptrm(t->r, i, j));
  }
  return t;
}*/

static trm_p mk_norm_lam(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&lams, ((uint64_t)tyno)<<10, t->id);
  if (lams.d[pos].data) return lams.d[pos].data;
  if (t->tag!=AP || t->r->tag!=DB || t->r->no!=0 || (t->l->fv2 & 1) != 0)
    return(hashtbli2_add_atpos(&lams, pos, ((uint64_t)tyno)<<10, t->id,
      add_tm(LAM, max32(0,t->maxv-1), tyno, t, NULL, t->size+1, t->fv1>>1, (t->fv2>>1) | ((t->fv1 & 1) << 127))));
  trm_p nt = uptrm(t->l, 0, -1); // Positions can change in uptrm, e.g. resize could happen
  return hashtbli2_add(&lams, ((uint64_t)tyno)<<10, t->id, nt);
}

static trm_p mk_norm_all(uint32_t tyno, trm_p t) {
  if (incomplete && (t->fv2 & 1) == 0)
    return uptrm(t, 0, -1);
  else
    return mk_all(tyno, t);
}

static bool is_fv_0(trm_p t, int32_t j) {
  return (j < 128) ? (((t->fv2 >> j) & 1) == 0) : (((t->fv1 >> j) & 1) == 0);
}

static trm_p subst_tt(trm_p t, int32_t j, trm_p s, int32_t depth) {
  if (!stasks[depth])
    alloc_stasks(depth);
  struct ftask *tasks=stasks[depth];
  uint32_t tasks_len=stasks_len[depth];
  bool istm=true; int32_t tl=0; trm_p t2, t3;
  while (true) {
    if (istm) {
      if (t->maxv <= j) {istm = false; continue; }
      if (is_fv_0(t, j)) {t=uptrm(t, j, -1); istm = false; continue; }
#ifdef CACHE_SUBST
      t2 = hashtbli3_find (&shsh, t->id, j << 10, s->id);
      if (t2) {istm = false; t = t2; continue; }
#endif
      if (tl >= tasks_len) {
        printf ("Extendings s-tasks to: %li MB\n", (tasks_len * sizeof(struct ftask)) >> 20);
        stasks[depth]=recalloc(stasks[depth], stasks_len[depth], stasks_len[depth] << 1, sizeof(struct ftask));
        stasks_len[depth] = stasks_len[depth] << 1;
        tasks=stasks[depth]; tasks_len=stasks_len[depth];
      }
      switch (t->tag) {
        case AP:  add_task5(&tasks[tl], TAPR,  t->r, j, t->id, j << 10); t=t->l; tl++; continue;
        case IMP: add_task5(&tasks[tl], TIMPR, t->r, j, t->id, j << 10); t=t->l; tl++; continue;
        case EQ:  add_task6(&tasks[tl], TEQR, t->r, t->no, j, t->id, j << 10); t=t->l; tl++; continue;
        case DB: istm = false; t = uptrm(s, 0, j); continue;
        case ALL: add_task4(&tasks[tl], TALL, t->no, t->id, j << 10); t=t->l; j++; tl++; continue;
        case LAM: add_task4(&tasks[tl], TLAM, t->no, t->id, j << 10); t=t->l; j++; tl++; continue;
        default: istm = false;
      }
    } else {
      if (tl <= 0) return t;
      tl--;
      switch (tasks[tl].ttag) {
        case TAPR: istm=true; t2=t; t=tasks[tl].t; j=tasks[tl].i; tasks[tl].ttag=TAPD; tasks[tl].t=t2; tl++; continue;
        case TAPD:
          t2 = tasks[tl].t; // left side of the application
          uint32_t subst_ret_pos = hashtbli2_find_index (&aps, t2->id, t->id);
          if (aps.d[subst_ret_pos].data)
            t = aps.d[subst_ret_pos].data;
          else {
            if (t2->tag!=LAM) {
              t3 = add_tm(AP, max32(t2->maxv,t->maxv), 0, t2, t, t2->size+t->size+1, t2->fv1 | t->fv1, t2->fv2 | t->fv2);
              t = hashtbli2_add_atpos(&aps, subst_ret_pos, t2->id, t->id, t3);
            } else t = subst_tt(t2->l, 0, t, depth + 1); // outside call
          }
          SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        case TIMPR: istm=true; t2=t; t=tasks[tl].t; j=tasks[tl].i; tasks[tl].ttag=TIMPD; tasks[tl].t=t2; tl++; continue;
        case TIMPD: t=mk_norm_imp(tasks[tl].t, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        case TEQR: istm=true; t2=t; t=tasks[tl].t; j=tasks[tl].i; tasks[tl].ttag=TEQD; tasks[tl].t=t2; tl++; continue;
        case TEQD: t=mk_norm_eq(tasks[tl].no, tasks[tl].t, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        case TALL: t=mk_norm_all(tasks[tl].no, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        case TLAM: t=mk_norm_lam(tasks[tl].no, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        default: fprintf(stderr, "SZS status Error: subst_tt: TNONE @ %i : %i\n", tl, tasks[tl].ttag); exit(2);
      }
    }
  }
}

static trm_p subst(trm_p t, int32_t j, trm_p s) {
  return subst_tt(t, j, s, 0);
}

/* Recursive version of subst without caching

static trm_p mk_norm_ap(trm_p l, trm_p r);
static trm_p subst(trm_p t, int32_t j, trm_p s) {
  if (t->maxv <= j)
    return t;
  if (is_fv_0(t, j))
    return uptrm(t, j, -1);
  switch (t->tag) {
  case DB:
    return uptrm(s, 0, j);
  case AP:
    return mk_norm_ap(subst(t->l, j, s), subst(t->r, j, s));
  case LAM:
    return mk_norm_lam(t->no, subst(t->l, (j + 1), s));
  case IMP:
    return mk_norm_imp(subst(t->l, j, s), subst(t->r, j, s));
  case ALL:
    return mk_all(t->no, subst(t->l, (j + 1), s));
  case EQ:
    return mk_norm_eq(t->no, subst(t->l, j, s), subst(t->r, j, s));
  }
  return t;
}
*/

static trm_p mk_norm_ap(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&aps, l->id, r->id);
  if (aps.d[pos].data) return aps.d[pos].data;
  if (l->tag!=LAM)
    return(hashtbli2_add_atpos(&aps, pos, l->id, r->id,
      add_tm(AP, max32(l->maxv,r->maxv), 0, l, r, l->size+r->size+1, l->fv1 | r->fv1, l->fv2 | r->fv2)));
  trm_p nt = subst(l->l, 0, r);  // Positions can change in subst
  return (hashtbli2_add(&aps, l->id, r->id, nt));
}

/*
enum ty_kind { NONE=0, PROP=1, BASE=2, AR=3 };

struct ty_struct {
  int16_t tag;
  uint32_t l; uint32_t r;
};
typedef struct ty_struct* ty_p;

static struct ty_struct **ty;
static uint32_t ty_len, ty_num;
static struct hashtbli1 bases;
static struct hashtbli2 ars;
static ty_p propp;
*/

static void init_tables() {
  tm = calloc(BLOCK_SIZE, sizeof(struct tm_struct *));
  x = 0; y = 0; y_len = 1;
  for (int i = 0; i < y_len; ++i)
    tm[i] = calloc(BLOCK_SIZE, sizeof(struct tm_struct));
  id = calloc(1 << 20, sizeof(uint8_t));
  idmaxelem = (1 << 20) - 1;
  for (int i = 0; i < 128; ++i)
    dbs[i] = add_tm(DB, i+1, i, NULL, NULL, 1, 0, ((unsigned __int128)1)<<i);
  for (int i = 128; i < 256; ++i)
    dbs[i] = add_tm(DB, i+1, i, NULL, NULL, 1, ((unsigned __int128)1)<<i, 0);
  vector_make(&names, 1 << 12);
  hashtbli2_make(&aps,   1 << 20);
  hashtbli2_make(&lams,  1 << 16);
  hashtbli2_make(&imps,  1 << 20);
  hashtbli2_make(&alls,  1 << 20);
  vector_make(&choices, 1 << 12);
  hashtbli3_make(&eqs,  1 << 20);
  tasks_len = 1 << 20; tasks = calloc(tasks_len, sizeof(struct ftask));
  // Allocate only on demand
  // alloc_stasks(0); alloc_stasks(1); alloc_stasks(2); alloc_stasks(3);
  start_x = x;
#ifdef CACHE_SUBST
  hashtbli3_make(&uhsh, 1 << 18);
  hashtbli3_make(&shsh, 1 << 20);
#endif
  vector_make(&atom2lit, 1 << 10);
  hashtbli1_make(&tmp_hash, 1 << 10);
  // Needs the other tables initialized
  falsep = add_tm(FAL, 0, 0, NULL, NULL, 1, 0, 0);
  truep = mk_imp(falsep, falsep);
  /*ty_len = 1 < 10;
  ty = calloc(ty_len, size_of(struct ty_struct));
  hashtbli1_make(&bases, 1 << 10);
  hashtbli2_make(&ars,   1 << 12);
  propp = */
}

#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/callback.h>

#define Tm_val(i)     (&tm[Int_val(i) >> 16][Int_val(i) & 0xFFFF])
static value Val_tm(trm_p p) {return Val_int((p->y << 16) | p->x);}

value c_mk_db(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_db(Int_val(n))));
}

value c_mk_name(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_name(Int_val(n))));
}

value c_mk_ap(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_ap(Tm_val(l), Tm_val(r))));
}

value c_mk_norm_ap(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_norm_ap(Tm_val(l), Tm_val(r))));
}

value c_mk_lam(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_lam(Int_val(n), Tm_val(r))));
}

value c_mk_norm_lam(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_norm_lam(Int_val(n), Tm_val(r))));
}

value c_mk_false(value unit) {
  CAMLparam1(unit);
  CAMLreturn(Val_tm(mk_false()));
}

value c_mk_imp(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_imp(Tm_val(l), Tm_val(r))));
}

value c_mk_norm_imp(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_norm_imp(Tm_val(l), Tm_val(r))));
}

value c_mk_all(value n, value r) {
  CAMLparam2(n, r);
  CAMLreturn(Val_tm(mk_norm_all(Int_val(n), Tm_val(r))));
}

value c_mk_choice(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_choice(Int_val(n))));
}

value c_mk_eq(value n, value l, value r) {
  CAMLparam3(n,l,r);
  CAMLreturn(Val_tm(mk_eq(Int_val(n), Tm_val(l), Tm_val(r))));
}

value c_mk_norm_eq(value n, value l, value r) {
  CAMLparam3(n,l,r);
  CAMLreturn(Val_tm(mk_norm_eq(Int_val(n), Tm_val(l), Tm_val(r))));
}

void c_init_tm_tables(value unit) {
  CAMLparam1(unit);
  init_tables();
  CAMLreturn0;
}

value c_uptrm(value t, value i, value j) {
  CAMLparam3(t,i,j);
  CAMLreturn(Val_tm(uptrm(Tm_val(t),Int_val(i),Int_val(j))));
}

value c_subst(value t, value i, value s) {
  CAMLparam3(t,i,s);
  CAMLreturn(Val_tm(subst(Tm_val(t),Int_val(i),Tm_val(s))));
}

value c_get_tag(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_int(Tm_val(t)->tag));
}

value c_get_no(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_long(Tm_val(t)->no));
}

value c_get_l(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_tm(Tm_val(t)->l));
}

value c_get_r(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_tm(Tm_val(t)->r));
}

value c_get_maxv(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_long(Tm_val(t)->maxv));
}

value c_get_fv0_0(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_bool((Tm_val(t)->fv2 & 1) == 0));
}

value c_get_fv0(value t, value i) {
  CAMLparam1(t);
  CAMLreturn(Val_bool(is_fv_0(Tm_val(t), Int_val(i))));
}

#define fst(a) Field(a, 0)
#define snd(a) Field(a, 1)

value c_get_head_spine(value _t) {
  CAMLparam1(_t);
  trm_p t = Tm_val(_t);
  CAMLlocal2(args, tmp);
  while (t->tag == AP) {
    tmp = caml_alloc_small(2, Tag_cons);
    fst(tmp) = Val_tm(t->r);
    snd(tmp) = args;
    args = tmp;
    t = t->l;
  }
  tmp = caml_alloc_tuple(2);
  fst(tmp) = Val_tm(t);
  snd(tmp) = args;
  CAMLreturn(tmp);
}

value c_get_head(value _t) {
  CAMLparam1(_t);
  trm_p t = Tm_val(_t);
  while (t->tag == AP)
    t = t->l;
  CAMLreturn(Val_tm(t));
}

value c_get_isneg(value _t) {
  CAMLparam1(_t);
  trm_p t = Tm_val(_t);
  CAMLreturn(Val_bool(t->tag==IMP && t->r->tag==FAL));
}

value c_get_nonnegated(value _t) {
  CAMLparam1(_t);
  trm_p t = Tm_val(_t);
  CAMLreturn(Val_tm((t->tag==IMP && t->r->tag==FAL) ? t->l : t));
}

void c_set_incomplete(value _b) {
  CAMLparam1(_b);
  incomplete = Bool_val(_b);
  CAMLreturn0;
}

void c_print(value t) {
  CAMLparam1(t);
  print(Tm_val(t)); printf("\n");
  fflush(stdout);
  CAMLreturn0;
}

/* Unimplemented
void c_hash_clear(value unit) {
  CAMLparam1(unit);
  vector_clear(&prims);
  vector_clear(&tmhs);
  hashtbli2_clear(&imps);
  hashtbli2_clear(&aps);
  hashtbli2_clear(&lams);
  hashtbli2_clear(&alls);
  tm_id_clear();
  hashtbli3_clear(&uhsh);
  hashtbli3_clear(&shsh);
  CAMLreturn0;
}
*/



static struct vector processed_indices;
static uint32_t processed_next = 0;

void c_processed_make(value len) {
  CAMLparam1(len);
  vector_make(&processed_indices, Int_val(len));
  CAMLreturn0;
}

void c_processed_add(value _t) {
  CAMLparam1(_t);
  trm_p t = Tm_val(_t);
  t->processed = true;
  if (processed_indices.len <= processed_next)
    vector_resize(&processed_indices, processed_indices.len << 1);
  processed_indices.data[processed_next++] = t;
  CAMLreturn0;
}

value c_processed_mem(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_bool(Tm_val(t)->processed));
}

void c_processed_clear(value unit) {
  CAMLparam1(unit);
  for (uint32_t i = 0; i < processed_next; ++i)
    ((trm_p)(processed_indices.data[i]))->processed = false;
  processed_next = 0;
  CAMLreturn0;
}

/* Usable but not needed



value c_hashtbli2_find(value hsh, value src1, value src2) {
  CAMLparam3(hsh, src1, src2);
  CAMLreturn(Val_long((long)(hashtbli2_find(Hashtbli2_val(hsh), Long_val(src1), Long_val(src2)))));
}




static struct custom_operations vectori_ops = {
  (char*)"vectori",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default
};

#define Vectori_val(v) ((struct vector *)Data_custom_val(v))
static value alloc_vectori() {
  return (alloc_custom(&vectori_ops, sizeof(struct vector), 0, 1));
}

value c_vectori_make(value len) {
  CAMLparam1(len);
  CAMLlocal1(ret);
  ret = alloc_vectori();
  vector_make(Vectori_val(ret), Int_val(len));
  CAMLreturn(ret);
}

void c_vectori_add(value _v, value i, value j) {
  CAMLparam3(_v, i, j);
  struct vector *v = Vectori_val(_v);
  while (v->len <= Long_val(i))
    vector_resize(v, v->len << 1);
  v->data[Long_val(i)] = (void*) Long_val(j);
  CAMLreturn0;
}

value c_vectori_find(value v, value i) {
  CAMLparam2(v, i);
  CAMLreturn(Val_long(Vectori_val(v)->data[Long_val(i)]));
}
*/

static int64_t get_literal(trm_p t) {
  int64_t ret = t->lit;
  if (ret == 0) {
    if ((t->tag==IMP) && (t->r->tag==FAL)) {
      ret = t->l->lit;
      if (ret == 0) {
        t->l->lit = next_atom;
        vector_pushback(&atom2lit, next_atom, t->l);
        ret = next_atom++;
      }
      ret = -ret;
      t->lit = ret;
    } else {
      t->lit = next_atom;
      vector_pushback(&atom2lit, next_atom, t);
      ret = next_atom++;
    }
  }
  return ret;
}

value c_get_literal(value _t) {
  CAMLparam1(_t);
  CAMLreturn(Val_long(get_literal(Tm_val(_t))));
}

value c_literal_to_trm(value _l) {
  CAMLparam1(_l);
  long l = Long_val(_l);
  trm_p t = (l < 0) ? mk_imp(atom2lit.data[-l], falsep) : atom2lit.data[l];
  CAMLreturn(Val_tm(t));
}

value c_max_atom(value unit) {
  CAMLparam1(unit);
  CAMLreturn(Val_long(next_atom - 1));
}

/*
static uint64_t tm_size2(trm_p t) {
  uint64_t ret = (long)hashtbli1_find(&tmp_hash, t->id);
  if (ret == 0) {
    ret = 1;
    switch (t->tag) {
    case AP: case IMP: case EQ:
      ret += tm_size2(t->r); // Intentional roll-over
    case LAM: case ALL:
      ret += tm_size2(t->l);
    }
    hashtbli1_add(&tmp_hash, t->id, (void*)ret);
  }
  return ret;
}
*/

value c_tm_size(value t) {
  CAMLparam1(t);
  //  hashtbli1_clear(&tmp_hash);    tm_size2...
  CAMLreturn(Val_long(Tm_val(t)->size));
}

static void unique_subterm_bottom_up_iter(value f, trm_p t) {
  if ((long)hashtbli1_find(&tmp_hash, t->id) == 0) {
    switch (t->tag) {
    case AP: case IMP: case EQ:
      unique_subterm_bottom_up_iter(f, t->r); // Intentional roll-over
    case LAM: case ALL:
      unique_subterm_bottom_up_iter(f, t->l);
    }
    caml_callback(f, Val_tm(t));
    hashtbli1_add(&tmp_hash, t->id, (void*)1);
  }
}

void c_unique_subterm_bottom_up_iter(value f, value t) {
  CAMLparam2(f, t);
  hashtbli1_clear(&tmp_hash);
  unique_subterm_bottom_up_iter(f, Tm_val(t));
  CAMLreturn0;
}

static trm_p unique_subterm_bottom_up_replace(value f, trm_p t) {
  trm_p ret = hashtbli1_find(&tmp_hash, t->id);
  trm_p l2, r2;
  if (!ret) {
    switch (t->tag) {
    case AP:
      l2 = unique_subterm_bottom_up_replace(f, t->l);
      r2 = unique_subterm_bottom_up_replace(f, t->r);
      t = mk_norm_ap(l2, r2);
      break;
    case IMP:
      l2 = unique_subterm_bottom_up_replace(f, t->l);
      r2 = unique_subterm_bottom_up_replace(f, t->r);
      t = mk_norm_imp(l2, r2);
      break;
    case EQ:
      l2 = unique_subterm_bottom_up_replace(f, t->l);
      r2 = unique_subterm_bottom_up_replace(f, t->r);
      t = mk_eq(t->no, l2, r2);
      break;
    case LAM:
      l2 = unique_subterm_bottom_up_replace(f, t->l);
      t = mk_norm_lam(t->no, l2);
      break;
    case ALL:
      l2 = unique_subterm_bottom_up_replace(f, t->l);
      t = mk_all(t->no, l2);
      break;
    }
    ret = Tm_val(caml_callback(f, Val_tm(t)));
    hashtbli1_add(&tmp_hash, t->id, ret);
  }
  return ret;
}

value c_unique_subterm_bottom_up_replace(value f, value t) {
  CAMLparam2(f, t);
  hashtbli1_clear(&tmp_hash);
  t = Val_tm(unique_subterm_bottom_up_replace(f, Tm_val(t)));
  CAMLreturn(t);
}
