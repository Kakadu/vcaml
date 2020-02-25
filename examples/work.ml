


let rec loop n =
  let a = ref 0 in

(*  let inner x =
    a := !a + x
  in

  inner n;*)
  let b = a in
  n


[@@@ prop.main (fun n -> loop n > 0)]
