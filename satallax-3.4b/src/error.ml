exception FileNotFound of string
exception GenericError of string
exception Redeclaration of string
exception IncompleteSatisfiable
exception Timeout

let remaining_time () =
  let a = Unix.getitimer Unix.ITIMER_REAL in
  a.Unix.it_value

(*** set_timer for timeout signal, see http://alan.petitepomme.net/cwn/2006.01.03.html#2 ***)
let set_timer s =
  ignore (Sys.signal Sys.sigalrm (Sys.Signal_handle (fun signo -> raise Timeout)));
  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = s });;

let set_sub_timer s =
  let z = remaining_time() in
  let s2 = min z s in
  let z2 = z -. s2 in
  let g x =
    if x > 0.0 then
      set_timer x
    else
      raise Timeout
  in
  let f () =
    let y = remaining_time() in
    g (z2 +.y)
  in
  if s2 <= 0.0 then raise Timeout;
  ignore (Sys.signal Sys.sigalrm (Sys.Signal_handle (fun signo -> g z2; raise Timeout)));
  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = s2 });
  ((),f);;
