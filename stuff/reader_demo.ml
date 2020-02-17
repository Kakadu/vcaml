module Reader = struct
  type ('r, 'a) t = { reader : 'r -> 'a }

  let run_reader { reader } = reader
  let reader f = { reader = f }
  let return x = { reader = (fun _ -> x) }
  let (>>=) x f = reader @@ fun r -> run_reader (f @@ run_reader x r) r
  let ask = reader (fun x -> x)
  let asks = reader


  module Syntax = struct
  (*  let (and+ ) o1 o2  = product o1 o2*)
    let (let* ) x f    = x >>= f
  (*  let (let+ ) x f    = x map f x*)
  end
end

open Reader

let example2 context : string =
  let open Syntax in
  let greet : string -> (string,string) Reader.t = fun name ->
    let* greeting = ask in
    return @@ Printf.sprintf "%s, %s" greeting name
  in
  let fin : string -> (string,string) Reader.t = fun input ->
    let* is_hello = asks ((=) "hello") in
    return @@ Printf.sprintf "%s%s" input (if is_hello then "!" else ".")
  in
  run_reader (greet "James" >>= fin) context

let () = print_endline @@ example2 "Hello"
