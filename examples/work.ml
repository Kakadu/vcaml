let a = ref 666


let loop1 n = a
[@@@ prop.main1 (fun m -> !(loop1 m) > 0)]


let loop2 n = !a
[@@@ prop.main2 (fun m -> (loop2 m) > 0)]
