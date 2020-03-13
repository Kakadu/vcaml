let a = ref 666


let loop1 n = a
[@@@ prop.main1 (fun m -> !(loop1 m) > 0)]


let loop2 n = !a
[@@@ prop.main2 (fun n -> (loop2 n) > 0)]
