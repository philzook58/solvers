let with_in fp f = let c = open_in fp in let i = f c in close_in c; i

let with_out fp f = let c = open_out fp in f c; close_out c
