let x = ref 0


let f y =
  x := !x + y;
  !x + y
