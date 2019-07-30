let gl = ref 0
let rec f x =
  gl := x+2;
  let () = gl := 1000 + x in
  (* let m = x + x inS *)
  f x
