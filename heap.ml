
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

type term = LI of (t[@sexp.opaque]) * Longident.t
          | CInt of int
          | BinOp of op * term * term
          | Unit
          | Call of Longident.t * term
          | Union of (pf * term) list
          | Lambda of { lam_argname: Longident.t option
                      (* ; lam_env: t *)
                      ; lam_body: term 
                      }
and pf  = LogicBinOp of logic_op * pf * pf 
        | Not of pf
        | Term of term
[@@deriving sexp_of]
and logic_op = Conj | Disj [@@deriving sexp_of]
and op = | Plus | Minus | LT | LE | GT | GE | Eq [@@deriving sexp_of]
and t = HAssoc of (Longident.t * term) list
        (* Heap should be a mapping from terms to terms (array access, for example)
         * but for fibonacci it doesn't matter
         *)
      | HMerge of (pf * t) list 
      | HCmps of t * t 
      | HEmpty
[@@deriving sexp_of]

(** Term operations *)
let call fident arg = Call (fident, arg)
let lambda lam_argname lam_env lam_body = Lambda { lam_argname; (* lam_env; *) lam_body }
let li h longident = LI (h,longident)
let union xs = Union xs
let union2 g1 t1 g2 t2 = union [(g1,t1); (g2,t2)]
let binop op a b = BinOp (op,a,b)

(** Propositonal formula operations *)
let pf_term el = Term el 
let pf_not pf = Not pf
let pf_binop op f1 f2 = LogicBinOp (op, f1, f2)


(** Heap operations *)
let cmps : t -> t -> t = fun a b -> 
  match (a,b) with 
  | (HEmpty,_) -> b
  | (_,HEmpty) -> a
  | (HAssoc xs, HAssoc ys) -> HAssoc (xs @ ys)
  | _ -> HCmps (a,b)
let empty : t = HEmpty
let single name el : t = HAssoc [(name,el)]
let merge2 g1 h1 g2 h2 = HMerge [(g1,h1); (g2,h2)]

(** The main heap access function *)
let hfind_exn ident heap = 
  match heap with 
  | _ -> raise Not_found

let hfind_li longident heap = 
  try hfind_exn longident heap 
  with Not_found -> li longident
