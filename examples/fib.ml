let fib n = 
  let a = ref 1 in
  let b = ref 1 in
  let rec loop n = 
    if n <= 1
    then ()
    else 
      let c = !a + !b in 
      let () = a := !b in
      let () = b := c in
      let m = n-1 in 
      loop m 
  in
  loop n;
  !b