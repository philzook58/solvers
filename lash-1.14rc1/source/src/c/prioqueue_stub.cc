#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>

#include <queue>

#define Queue_val(v) (*((std::priority_queue<int, std::vector<int>, std::greater<int> > **)Data_custom_val(v)))

static struct custom_operations queue_ops = {
  (char*)"queue",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default
};

extern "C" value c_pq_make (value unit) {
  CAMLparam1(unit);
  CAMLlocal1(r);
  r=alloc_custom(&queue_ops, sizeof(std::priority_queue<int, std::vector<int>, std::greater<int> > *), 0, 1);
  Queue_val(r) = new std::priority_queue<int, std::vector<int>, std::greater<int> >();
  CAMLreturn(r);
}

extern "C" void c_pq_push (value pq, value i) {
  CAMLparam2(pq, i);
  Queue_val(pq)->push(Long_val(i));
  CAMLreturn0;
}

extern "C" value c_pq_top (value _pq) {
  CAMLparam1(_pq);
  const auto pq = Queue_val(_pq);
  CAMLreturn(Val_long(pq->empty() ? -1 : pq->top()));
}

extern "C" void c_pq_pop (value pq) {
  CAMLparam1(pq);
  Queue_val(pq)->pop();
  CAMLreturn0;
}
