let a = ref 400


let loop n =
  !a

[@@@ prop.main (fun m -> loop m > 0)]
