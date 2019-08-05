


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
      (* let m =  in  *)
      loop (n-1) 
  in
  loop n;
  !b