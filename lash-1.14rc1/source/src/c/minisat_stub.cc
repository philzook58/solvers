/* File: Ointerface.cc
 * Author: Chad E. Brown, Nov 30, 2010 -- Updated Nov, 2011 for Minisat 2.2.0
 * OCaml interface to MiniSat used by Satallax
 * Code based on Main.C in MiniSat (Niklas Eeen, Niklas Sorensson)
 * and MiniSat-ocaml (Flavio Lerda, Pietro Abate).
 * Also used Chapter 25 of _Practical OCaml_ Joshua B. Smith.
 * The most useful thing I found was the tutorial "How to wrap C functions to OCaml" by Florent Monnier:
 * http://www.linux-nantes.org/~fmonnier/ocaml/ocaml-wrapping-c.php
 */

#include "simp/SimpSolver.h"
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>

using namespace Minisat;
static Solver* solver; // Simp
static vec<Lit> lits;
static bool redirect = true;

extern "C" void minisat_init(value _log) {
  CAMLparam1(_log);
  if (solver != NULL)
    delete solver;
  solver = new Solver; // Simp
  //solver->use_elim = false;
  if (redirect && (Int_val(_log) < 10)) {  // redirect stderr to avoid reportf info being printed
    FILE* ignore = freopen("/dev/null", "w", stderr);
    redirect = false;
  }
  CAMLreturn0;
}

static Lit litof (int p) {
  int var = abs(p)-1;
  while (var >= (*solver).nVars())
    Var v = (*solver).newVar();
  return (mkLit(var,(p > 0)));
}

extern "C" value minisat_addClause(value l) {
  CAMLparam1(l);
  lits.clear();
  for (; l != Val_emptylist; l = Field(l, 1))
    lits.push(litof(Int_val(Field(l, 0))));
  CAMLreturn(Val_bool(solver->addClause_(lits)));
}

extern "C" value minisat_search (value unit) {
  CAMLparam1(unit);
  CAMLreturn(Val_bool(solver->simplify() && solver->solve()));
}

// search, with 1 assumed lit
extern "C" value minisat_search1 (value _lit) {
  CAMLparam1(_lit);
  int lit = Int_val(_lit);
  int var = abs(lit)-1;
  CAMLreturn(Val_bool(var < (*solver).nVars() || solver->solve(litof(lit))));
}

// get the value of a variable
// return value: 0 true, 1 false, 2 undefined
extern "C" value modelValue (value _lit) {
  CAMLparam1(_lit);
  int lit = Int_val(_lit);
  int var = abs(lit)-1;
  int ret = 3;
  if (var < (*solver).nVars()) {
    ret = toInt(solver->modelValue(litof(lit)));
  }
  CAMLreturn(Val_int(ret));
}
