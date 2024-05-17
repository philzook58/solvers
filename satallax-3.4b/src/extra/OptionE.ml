let is_some = function
  Some _ -> true
| None   -> false

let mapm f = function
  Some x -> f x
| None   -> ()
