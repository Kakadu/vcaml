module MyIdent = struct
  type longident = [%import: Longident.t] [@@deriving sexp_of]

  type t = Ident.t
  let to_string ident = Ident.unique_name ident
   (* Sexplib.Sexp.to_string_hum @@ sexp_of_t ident *)
  let sexp_of_t ident  = to_string ident |> Sexplib.Std.sexp_of_string
  let pp_string () = to_string
  let equal = Ident.equal
end

type cre_mode = Assign | Const [@@deriving sexp_of]
let pp_longident () lident = Longident.flatten lident |> String.concat ~sep:"."
type term = LI of heap option * MyIdent.t
          | CInt of int
          | BinOp of op * term * term
          | Unit
          | Call of term * term
          | Union of (pf * term) list
          | Lambda of { lam_argname: MyIdent.t option
                      ; lam_api   : api
                      ; lam_eff   : heap
                      ; lam_body  : term
                      ; lam_is_rec: bool
                      }
and api = (MyIdent.t * term) list [@@deriving sexp_of]
(* TODO: it should be path here *)
and t = HAssoc of (MyIdent.t * (cre_mode * term)) list
        (* Heap should be a mapping from terms to terms (array access, for example)
         * but for fibonacci it doesn't matter
         *)
      | HMerge of (pf * t) list
      | HCmps of heap * heap
      | HCall of term * term
      | HEmpty
[@@deriving sexp_of]
and pf  = LogicBinOp of logic_op * pf * pf
        | Not of pf
        | Term of term
[@@deriving sexp_of]
and logic_op = Conj | Disj [@@deriving sexp_of]
and op = | Plus | Minus | LT | LE | GT | GE | Eq [@@deriving sexp_of]
and heap = t [@@deriving sexp_of]
let pp_term () t = Sexplib.Sexp.to_string @@ sexp_of_term t
let pp_heap () h = Sexplib.Sexp.to_string @@ sexp_of_heap h
(** Term operations *)
let call fexpr arg = 
  Format.eprintf "constructing call of '%s' to '%s'\n"  (pp_term () fexpr)  (pp_term () arg);
  Call (fexpr, arg)
let lambda lam_is_rec lam_argname lam_api lam_eff lam_body =
  Lambda { lam_argname; lam_api; lam_eff; lam_body; lam_is_rec }
let li ?heap longident = LI (heap, longident)
let union xs = Union xs
let union2 g1 t1 g2 t2 = union [(g1,t1); (g2,t2)]
let binop op a b = BinOp (op,a,b)

(** Propositonal formula operations *)
let pf_term el = Term el
let pf_not pf = Not pf
let pf_binop op f1 f2 = LogicBinOp (op, f1, f2)


(** Heap operations *)
let hcmps : t -> t -> t = fun a b ->
  Format.eprintf "calling hcmps of\n%!";
  Format.eprintf "\t%s\n%!" (pp_heap () a);
  Format.eprintf "\t%s\n%!" (pp_heap () b);
  match (a,b) with
  | (HEmpty,b) -> b
  | (a,HEmpty) -> a
  | (HAssoc xs, HAssoc ys) -> HAssoc (xs @ ys)
  | _ -> HCmps (a,b)
let hempty : t = HEmpty
(* let hsingle name el : t = HAssoc [(name,el)] *)
let hassign name el : t = HAssoc [(name, (Assign, el))] 
let hconst name el : t =  HAssoc [(name, (Const, el))] 
let hmerge2 g1 h1 g2 h2 = HMerge [(g1,h1); (g2,h2)]

let hcall f x = HCall (f,x)

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
let rec hfind_li (heap: heap) longident : term =
  (* let (>>=) = Option.(>>=) in  *)
  let default = li ~heap longident in
  match heap with
  | HAssoc xs -> List.Assoc.find xs ~equal:MyIdent.equal longident
                 |> Option.value_map ~f:(fun (_,t) -> t) ~default
  | HEmpty -> default
  | HMerge hs ->
      union @@ List.map hs ~f:(fun (g,h) -> (g, hfind_li h longident))
  | HCmps (a,b) ->
      fat_dot a (hfind_li b longident)
  | HCall (_,_) -> default

and fat_dot (heap: t) term =
  match term with
  | Unit -> term
  | CInt _ -> term
  | LI (None, longident) -> hfind_li heap longident
  | LI (Some _h, longident) ->
      Format.eprintf "I don't know what to do in this case %s %d\n%!" __FILE__ __LINE__;
      hfind_li heap longident
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

let rec heap_subst heap lident new_term = 
  Format.eprintf "heap_subst not implemented\n%!";
  heap
and term_subst term lident new_term = 
  Format.eprintf "heap_subst not implemented\n%!";
  term

module Api = struct
  type t = api * MyIdent.t list
  let empty = ([],[])
  
  let add (api,pen) k v =
    (List.Assoc.add ~equal:MyIdent.equal api k v, pen)

  let add_pending (api,xs) new_ = (api,new_::xs)

  let remove_pending_exn (api,xs) el = (api, List.filter xs ~f:(MyIdent.equal el))

  let is_pending (_,xs) ident : bool = Base.List.exists xs ~f:(MyIdent.equal ident)
  (* let is_pending_lident (_,xs) (lident: Longident.t) : MyIdent.t option =
    assert false *)
  let find_ident_exn : t -> Ident.t -> term = fun (api,toplevel) ident ->
    List.Assoc.find_exn ~equal:MyIdent.equal api ident
  let find_ident_li : t -> Ident.t -> term = fun (api,toplevel) ident ->
    try find_ident_exn (api,toplevel) ident 
    with Not_found -> li ident
    
  
end
