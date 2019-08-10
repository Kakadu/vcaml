(* let g0 = ref 500
let f x = !g0
let ans1 = f (g0 := 100 - !g0) *)


(* let g1 = ref 500
let f x y = !g1
let ans1 = f (g1 := 100 - !g1) (g1 := 1000 - !g1) *)


let g2 = ref 500
let f x y = !g2
let ans2 = f (g2 := 1000 - !g2) (g2 := 100 - !g2)
