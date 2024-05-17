let tail s = String.sub s 1 (String.length s - 1)

let starts_with init s =
  let l = String.length init in
  String.length s >= l && String.sub s 0 l = init
