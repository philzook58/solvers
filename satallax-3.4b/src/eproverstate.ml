let prop_fo_forms = ref []
let stp_fo_forms = Hashtbl.create 10
let fo_types_h = Hashtbl.create 10
let fo_types = ref []
let fo_ecounter = Hashtbl.create 10
let atom_fof = Hashtbl.create 10
let lfth_ecounter = ref 0

let reset_eprover_state () =
  prop_fo_forms := [];
  Hashtbl.clear stp_fo_forms;
  Hashtbl.clear fo_types_h;
  fo_types := [];
  Hashtbl.clear fo_ecounter;
  Hashtbl.clear atom_fof;
  lfth_ecounter := 0
