let gl = ref 0

let foo () = gl := !gl + 2
let boo () = gl := !gl + 20
let goo () = boo(); foo ()
(* let rec f n = 
  if n<0 then ()
  else gl := !gl + 1

let g m =
  f m;
  !gl *)

(* let h () =
  let n = Random.int 0 in
  x := 42;
  g n *)
