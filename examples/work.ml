let x = ref 400


let loop n =
  !x + n


[@@@ prop.main (fun n -> loop n > 0)]
