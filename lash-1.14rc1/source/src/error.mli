exception FileNotFound of string
exception GenericError of string
exception Redeclaration of string
exception IncompleteSatisfiable
exception Timeout

val set_timer : float -> unit
val set_sub_timer : float -> unit * (unit -> unit)
val remaining_time : unit -> float
