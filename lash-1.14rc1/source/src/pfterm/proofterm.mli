open Refut

val print_coq_proofscript : out_channel -> refut -> unit

val print_tstp : out_channel -> refut -> unit

val print_coq_sproofterm : out_channel -> refut -> unit

val print_hocore : out_channel -> refut -> unit
val print_pfinfo : out_channel -> refut -> unit
val print_pfuseful : out_channel -> refut -> string option -> unit
val print_pfformdeps : out_channel -> refut -> string option -> unit

val refut_trms : refut -> Syntax.trm list
