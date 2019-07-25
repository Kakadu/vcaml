let x = ref 0
let rec f n =
  if n<=0 then ()
  else incr x

(* let g n =
  f n;
  !x

let h () =
  let n = Random.int 0 in
  x := 42;
  g n *)
