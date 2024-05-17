type 'a t = {mutable data: 'a array; item: 'a};;
let make len item = {data=Array.make len item; item=item};;
let get v i = v.data.(i);;
let get_default v i d =
  if i < Array.length v.data then Array.unsafe_get v.data i else d;;
let double v =
  let ndata = Array.make (2 * Array.length v.data) v.item in
  Array.blit v.data 0 ndata 0 (Array.length v.data);
  v.data <- ndata;;
let set v i j =
  while (Array.length v.data <= i) do double v done;
  Array.unsafe_set v.data i j;;
let update v i f =
  while (Array.length v.data <= i) do double v done;
  Array.unsafe_set v.data i (f (Array.unsafe_get v.data i));;
let iter f v =
  for i = 0 to Array.length v.data - 1 do f i (Array.unsafe_get v.data i) done;;
let clear v =
  for i = 0 to Array.length v.data - 1 do Array.unsafe_set v.data i v.item done;;

type 'a dynamic = {mutable data: 'a array; init: int -> 'a};;
let dynamic_make len init_fn = {data= Array.init len init_fn; init=init_fn};;
