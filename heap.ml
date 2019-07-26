module Longident = struct
  type t = [%import: Longident.t] [@@deriving sexp_of]
  let to_string ident = Sexplib.Sexp.to_string_hum @@ sexp_of_t ident
  let pp_string () = to_string
  let equal = Caml.(==)
end

type term = LI of (heap [@sexp.opaque]) * Longident.t
          | CInt of int
          | BinOp of op * term * term
          | Unit
          | Call of term * term
          | Union of (pf * term) list
          | Lambda of { lam_argname: Longident.t option
                      ; lam_api : (api [@sexp.opaque])
                      ; lam_eff: heap
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
and heap = t [@@deriving sexp_of]
and api = (Longident.t * term) list [@@deriving sexp_of]
let pp_term () t = Sexplib.Sexp.to_string @@ sexp_of_term t
(** Term operations *)
let call fexpr arg = Call (fexpr, arg)
let lambda lam_argname lam_api lam_eff lam_body = Lambda { lam_argname; lam_api; lam_eff; lam_body }
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

(* * The main heap access function a.k.a. READ
let rec hfind_exn (heap: heap) ident : term =
  match hfind heap ident with
  | None -> raise Not_found
  | Some ans -> ans
and hfind heap ident = 
  match heap with 
  | HAssoc xs -> List.Assoc.find xs ~equal:Longident.equal ident 
  | HEmpty -> None 
  | HMerge hs -> 
      List.fold_right ~init:[] hs ~f:()
      union @@ List.map hs ~f:(fun (g,h) -> (g, hfind)
  | HCmps (_,_) -> assert false *)
let rec hfind_li heap longident =
  (* let (>>=) = Option.(>>=) in  *)
  let default = li heap longident in 
  match heap with 
  | HAssoc xs -> List.Assoc.find xs ~equal:Longident.equal longident
                 |> Option.value_map ~f:(fun t -> t) ~default
  | HEmpty -> default
  | HMerge hs ->      
      union @@ List.map hs ~f:(fun (g,h) -> (g, hfind_li h longident))
  | HCmps (a,b) -> 
      fat_dot a (hfind_li b longident)
  

and fat_dot heap term = 
  match term with 
  | Unit -> term 
  | CInt _ -> term
  | LI (heap, longident) -> hfind_li heap longident
  | BinOp (op,l,r) -> BinOp (op, fat_dot heap l, fat_dot heap r)
  | Call (f, arg) -> Call (fat_dot heap f, fat_dot heap arg)
  | Union xs -> union @@ List.map xs ~f:(fun (pf,t) -> (fat_dot_pf heap pf, fat_dot heap t))
  | Lambda  { lam_argname; lam_eff; lam_body } -> 
      let () = Format.eprintf "Probably not implemented in %s %d" __FILE__ __LINE__ in 
      term
and simplify_term term = term
and fat_dot_pf heap pf = match pf with 
  | LogicBinOp (op, l, r) -> LogicBinOp (op, fat_dot_pf heap l, fat_dot_pf heap r)
  | Not pf -> Not (fat_dot_pf heap pf)
  | Term t -> Term (fat_dot heap t)
and simplify_pf pf = pf

let rec heap_subst heap lident new_term = heap 
and term_subst term lident new_term = term

module Api = struct 
  type t = api
  let find_exn (xs:t) k = List.Assoc.find_exn xs k ~equal:Longident.equal
  let add = List.Assoc.add ~equal:Longident.equal
end 