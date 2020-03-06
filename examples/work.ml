let x = ref 400


let loop n =
  !x + n


[@@@ prop.main (fun m -> loop m > 0)]
