
(* module Ident = struct
  include Ident
  let sexp_of_t ident =
    let b = Buffer.create 20 in
    let fmt = Format.formatter_of_buffer b in
    Ident.print fmt ident;
    Format.pp_print_flush fmt ();
    Sexplib.Sexp.Atom (Buffer.contents b)
end *)
module Longident = struct
  type t = [%import: Longident.t] [@@deriving sexp_of]
end

type el = LI of Longident.t
        | CInt of int
        | Unit
        | Call of Longident.t * el
        | Union of (pf * el) list
and pf = BinOp of op * el * el
       | Term of el
[@@deriving sexp_of]
and op = LT | LE | GT | GE | Eq [@@deriving sexp_of]
and t = (Longident.t * el) list
[@@deriving sexp_of]

let empty : t = []
let single name el : t = [(name,el)]
let call fident arg = Call (fident, arg)
let li longident = LI longident

let union xs = Union xs
let cmps : t -> t -> t = fun a b -> a
