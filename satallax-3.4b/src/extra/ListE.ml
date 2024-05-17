(* run function on list until function returns [] *)
let rec iterate f = function
  [] -> ()
| xs -> let ys = f xs in iterate f ys

let rec take n l = match n with
  0 -> []
| n -> begin match l with hd::tl -> hd::take (n-1) tl | [] -> [] end

let rec drop n l = match n with
  0 -> l
| n -> begin match l with hd::tl -> drop (n-1) tl | [] -> [] end
