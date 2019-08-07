let failwiths fmt = Format.kprintf failwith fmt
let (>>=?) = Option.(>>=)

module MyIdent = struct
  type longident = Longident.t =
    | Lident of GT.string
    | Ldot of longident * GT.string
    | Lapply of longident * longident
    [@@deriving gt ~options:{ fmt }]

  type t = Ident.t
  let to_string ident = Ident.unique_name ident
  (* let sexp_of_t ident  = to_string ident |> Sexplib.Std.sexp_of_string *)
  let pp_string () = to_string
  let equal = Ident.equal

  let t = { GT.gcata = (fun _ _ _ -> assert false)
          ; GT.plugins = object
              method fmt fmt o = Format.fprintf fmt "%s" (Ident.unique_name o)
              method gmap x = x
              method eq = equal
          end
          ; GT.fix = (fun _ -> assert false)
          }
end
module MyTypes = struct
  type type_expr = Types.type_expr

  let type_expr =
          { GT.gcata = (fun _ _ _ -> assert false)
          ; GT.plugins = object
              method fmt fmt _ = Format.fprintf fmt "<a type>"
              method gmap x = x
              method eq = phys_equal
          end
          ; GT.fix = (fun _ -> assert false)
          }
end

(* type cre_mode = Assign | Const [@@deriving gt ~options:{ fmt }] *)
let pp_longident () lident = Longident.flatten lident |> String.concat ~sep:"."

type logic_op = Conj | Disj [@@deriving gt ~options:{ fmt; gmap; eq }]
type op = | Plus | Minus | LT | LE | GT | GE | Eq [@@deriving gt ~options:{ fmt; gmap; eq }]

type 'term pf = LogicBinOp of logic_op * 'term pf * 'term pf
              | Not of 'term pf
              | EQident of MyIdent.t * MyIdent.t
              | PFTrue
              | PFFalse
              | Term of 'term
[@@deriving gt ~options:{ fmt; gmap; eq }]

type mem_repr = MemLeaf of int
              | MemBlock of {mem_tag: int; mem_sz: int; mem_cnt: mem_repr list }

(* **)
type api = (MyIdent.t * term) GT.list
and term  = CInt  of GT.int
          | CBool of GT.bool
          | Unit
          (* int,bool and unit doesn't need types because we have them in Predef module *)
          | LI of heap GT.option * MyIdent.t * MyTypes.type_expr
          | BinOp of op * term * term * MyTypes.type_expr
          | Call of term * term * MyTypes.type_expr
          | Union of (term pf * term) GT.list
          | Lambda of { lam_argname: MyIdent.t GT.option
                      ; lam_api    : api
                      ; lam_eff    : heap
                      ; lam_body   : term
                      ; lam_is_rec : GT.bool
                      ; lam_typ    : MyTypes.type_expr
                      }
(* TODO: it should be path here *)
and t = HDefined of (MyIdent.t * term) GT.list
        (* Heap should be a mapping from terms to terms (array access, for example)
         * but for fibonacci it doesn't matter
         *)
      | HMerge of (term pf * t) GT.list
      | HWrite of t * MyIdent.t * term
      | HCmps of heap * heap
      | HCall of term * term
      | HEmpty


and heap = t [@@deriving gt ~options:{ fmt; eq }]

type defined_heap = (MyIdent.t * term) list

module Defined = struct
  type t = defined_heap
  let filter = List.filter
  let add xs k v =  (k,v) :: xs
  let hacky_fold ~cond ~f xs =
    List.fold_left xs ~init:([],[]) ~f:(fun (bad, acc) (k,v) ->
      if cond k v
      then (k::bad, add acc k (f k v))
      else (bad,    add acc k v)
    )
  let has_key xs k =
    try ignore (List.Assoc.find_exn xs k ~equal:MyIdent.equal); true
    with Not_found -> false

  let equal xs ys ~f =
    Int.equal (List.length xs) (List.length ys) &&
    List.for_all xs ~f:(fun (k,v) ->
      match List.Assoc.find ys ~equal:MyIdent.equal k with
      | None -> false
      | Some v2 -> f v v2
    )
end

(* Pretty-printing boilerplate now *)

let fmt_op fmt = function
  | Plus  -> Format.fprintf fmt "+"
  | Minus -> Format.fprintf fmt "-"
  | LT    -> Format.fprintf fmt "<"
  | GT    -> Format.fprintf fmt ">"
  | LE    -> Format.fprintf fmt "≤"
  | GE    -> Format.fprintf fmt "≥"
  | Eq    -> Format.fprintf fmt "="

let fmt_logic_op fmt = function
  | Conj -> Format.fprintf fmt "∧"
  | Disj -> Format.fprintf fmt "∨"

class ['a, 'extra_pf] my_fmt_pf for_term fself_pf =
  object
    inherit ['a, 'extra_pf] fmt_pf_t for_term fself_pf
    method! c_LogicBinOp fmt _ op l r =
      Format.fprintf fmt "@[(@,%a@ %a@ %a@,)@]"
        fself_pf l
        fmt_logic_op op
        fself_pf r
    method! c_Not fmt subj f =
      match subj with
      | Not (EQident (l,r)) ->
          Format.fprintf fmt "@[(%a@ ≠@ %a)@]" (GT.fmt MyIdent.t) l (GT.fmt MyIdent.t) r
      | Not (Term (BinOp (LE,l,r,typ))) -> for_term fmt (BinOp (GT,l,r, typ))
      | Not (Term (BinOp (GT,l,r,typ))) -> for_term fmt (BinOp (LE,l,r, typ))
      | _ -> Format.fprintf fmt "¬%a" fself_pf f
    method! c_EQident fmt _ l r =
      Format.fprintf fmt "@[(%a@ =@ %a)@]"
        (GT.fmt MyIdent.t ) l
        (GT.fmt MyIdent.t ) r
    method! c_PFTrue  fmt _ = Format.fprintf fmt "TRUE"
    method! c_PFFalse fmt _ = Format.fprintf fmt "FALSE"
    method! c_Term fmt _ t =
      Format.fprintf fmt "@[%a@]" for_term t
  end

let pf =
  {
    GT.gcata = gcata_pf;
    GT.fix = (fun eta -> GT.transform_gc gcata_pf eta);
    GT.plugins = object
      method fmt fa = GT.transform_gc gcata_pf (new my_fmt_pf fa)
      method gmap  = pf.plugins#gmap
    end
  }

class ['extra_term] my_fmt_term
    ((for_api, for_t, fself_term,for_heap) as _mutuals_pack)
  =
  object
    inherit  ['extra_term] fmt_term_t_stub _mutuals_pack
    method! c_Lambda fmt _ _x__090_ _api heap term flg _ =
      Format.fprintf fmt "(Lambda @[<v>{ ";
      Format.fprintf fmt "@[lam_argname@ =@ %a@]@," (GT.fmt GT.option (GT.fmt MyIdent.t)) _x__090_;
      (* Format.fprintf fmt "@[; @[lam_api@ =@ %a@]@]@," for_api _x__091_; *)
      Format.fprintf fmt "@[; @[lam_eff@ =@ %a@]@]@,"  for_heap heap;
      Format.fprintf fmt "@[; @[lam_body@ =@ %a@]@]@," fself_term term;
      Format.fprintf fmt "@[; @[lam_is_rec@ =@ %b@]@]" flg;
      Format.fprintf fmt "})@]"
    method! c_BinOp inh___079_ _ op l r _typ =
      Format.fprintf inh___079_ "@[(@,%a@ %a@,@ %a)@]"
        fself_term l
        fmt_op op
        fself_term r
    method! c_CInt fmt _ n = Format.fprintf fmt "%d" n
    method! c_LI fmt _ h ident _typ =
      match h with
      | None -> Format.fprintf fmt "@[\"%a\"@]" (GT.fmt MyIdent.t) ident
      | Some h ->
          (* Format.fprintf fmt "LI@ @[(@,%a,@,@ \"%a\"@,)@]" for_heap h (GT.fmt MyIdent.t) ident *)
          Format.fprintf fmt "LI@ @[(@,...,@,@ \"%a\"@,)@]"  (GT.fmt MyIdent.t) ident
    method! c_Union fmt _ ps =
      (* TODO: normal printing *)
      Format.fprintf fmt "@[(Union@ ";
      GT.list.GT.plugins#fmt (fun fmt (l,r) ->
        Format.fprintf fmt "@[⦗@,@[%a@], @[%a@]@,⦘@]" (GT.fmt pf fself_term) l fself_term r
      ) fmt ps;
      (* List.iter ps ~f:(fun (l,r) ->
        Format.fprintf fmt "@[; @[⦗@,@[%a@], @[%a@]@,⦘@]@]" for_pf l fself_term r
      ); *)
      Format.fprintf fmt ")@]";
      (* Format.fprintf fmt "Union@ @[(@,%a@,)@]"
        (GT.fmt GT.list
            (fun fmt (l,r) -> Format.fprintf fmt "(%a,%a)" for_pf l fself_term r)
        ) _x__088_; *)
      ()
    method c_Call fmt _ f arg _typ =
      Format.fprintf fmt "Call@ @[(@,%a,@,@ %a@,)@]" fself_term f fself_term arg

  end

class ['extra_api] my_fmt_api
    ((for_api, for_t, for_term,for_heap) as _mutuals_pack)
  =
  object
    inherit  ['extra_api] fmt_api_t_stub _mutuals_pack
    inherit  (([(MyIdent.t * term),'extra_api] GT.fmt_list_t)
      (fun inh (l,r) ->
          Format.fprintf inh "%a@ ↦@ %a" (GT.fmt MyIdent.t) l
              for_term r
      )
      for_api)
    method! c_Nil fmt _ = Format.fprintf fmt "[]"
    method! c_Cons fmt xs _ _ =
      match xs with
      | [] -> Format.fprintf fmt "[]"
      | (k,v)::xs ->
          Format.open_vbox 0;
          Format.fprintf fmt   "@[<hov>[@ %a@ ↦@ %a@]@]@," (GT.fmt MyIdent.t) k for_term v;
          List.iter xs ~f:(fun (l,r) ->
            Format.fprintf fmt "@[<hov>;@ %a@ ↦@ %a@]@]@," (GT.fmt MyIdent.t) l for_term r
          );
          Format.fprintf fmt "@ ]"

  end

class ['extra_t] my_fmt_t ((for_api, fself_t, for_term, for_heap) as _mutuals_pack)
  =
  object
    inherit  ['extra_t] fmt_t_t_stub _mutuals_pack

    method! c_HDefined fmt _ xs =
      match xs with
      | [] -> Format.fprintf fmt "⟦⟧"
      | (hi,ht)::xs ->
          Format.open_hovbox 0;
          Format.fprintf fmt   "@[⟦ ⦗%a,@ %a⦘@]" (GT.fmt MyIdent.t) hi for_term ht;
          List.iter xs ~f:(fun (ident,term) ->
            Format.fprintf fmt "@[; ⦗%a,@ %a⦘@]" (GT.fmt MyIdent.t) ident for_term term
          );
          Format.fprintf fmt "⟧";
          Format.close_box ()
    method! c_HCmps fmt _ l r =
      Format.fprintf fmt "@[(%a@ ∘@ %a)@]" for_heap l for_heap r
    method c_HCall fmt _ f arg =
      Format.fprintf fmt "@[(RecApp@ @[(@,%a,@,@ %a@,)@])@]"
        for_term f for_term arg
    method c_HMerge fmt _ _x__066_ =
      Format.fprintf fmt "@[(HMerge@ @[";
      Format.fprintf fmt "%a" (GT.fmt GT.list (GT.fmt GT.tuple2 (GT.fmt pf for_term) fself_t)) _x__066_;
      Format.fprintf fmt "@])@]"

    method! c_HEmpty fmt _ = Format.fprintf fmt "ε"
  end

let fmt_term_0 = new my_fmt_term
let fmt_api_0 = new my_fmt_api
let fmt_t_0 = new my_fmt_t
let fmt_heap_0 = fmt_t_0
let fmt_api eta =
  let (f, _, _, _) =
    fix_api fmt_api_0  fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_t eta =
  let (_, f, _, _) =
    fix_api fmt_api_0  fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_term eta =
  let (_, _, f, _) =
    fix_api fmt_api_0  fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_heap eta =
  let (_, _, _, f) =
    fix_api fmt_api_0  fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta

let api = {
    GT.gcata = gcata_api;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_api end)
  }
let _ = api

let t = {
    GT.gcata = gcata_t;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_t end)
  }
let _ = t
let term =  {
    GT.gcata = gcata_term;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_term end)
  }
let _ = term
let heap = {
    GT.gcata = gcata_heap;
    GT.fix = fix_api;
    GT.plugins = object
      method fmt = fmt_heap
      method eq = eq_heap
    end
  }

(* End of Pretty-printing boilerplate *)
