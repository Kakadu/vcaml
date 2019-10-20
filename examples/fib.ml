
let a = ref 0
let b = ref 0
let rec loop n =
  if n <= 1
  then ()
  else
    let c = !a + !b in
    let () = a := !b in
    b := c;
    loop (n-1)

let fib ndx =
  a := 1;
  b := 1;
  loop ndx;
  !b

[@@@ prop      (fun n -> fib n > n)]
[@@@ prop.asdf (fun n -> fib n > n)]
