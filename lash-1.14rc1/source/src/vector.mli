type 'a t
val make : int -> 'a -> 'a t
val update : 'a t -> int -> ('a -> 'a) -> unit
val set : 'a t -> int -> 'a -> unit
val iter : (int -> 'a -> unit) -> 'a t -> unit
val clear : 'a t -> unit
val get_default : 'a t -> int -> 'a -> 'a
val get : 'a t -> int -> 'a

type 'a dynamic
val dynamic_make : int -> (int -> 'a) -> 'a dynamic
