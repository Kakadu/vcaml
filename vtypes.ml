let failwiths fmt = Format.kprintf failwith fmt
let (>>=?) = Option.(>>=)
let comparison_of_int ans =
  if ans < 0 then GT.LT else
  if ans = 0 then GT.EQ else
  GT.GT

let int_of_comparison = function
| GT.LT -> -1
| GT.EQ -> 0
| GT.GT -> 1

module MyIdent = struct
  type longident = Longident.t =
    | Lident of GT.string
    | Ldot of longident * GT.string
    | Lapply of longident * longident
    [@@deriving gt ~options:{ fmt }]

  type t = Ident.t
  let to_string ident = Ident.unique_name ident
  let pp_string () = to_string
  let equal = Ident.equal

  let t = { GT.gcata = (fun _ _ _ -> assert false)
          ; GT.plugins = object
              method fmt fmt o = Format.fprintf fmt "%s" (Ident.unique_name o)
              method gmap (x: t) = x
              method eq = equal
              method compare x y =
                comparison_of_int @@ Ident.compare x y
          end
          ; GT.fix = (fun _ -> assert false)
          }

  module Map = struct
    include Ident.Map

    class ['ia,'a,'sa, 'i, 'self, 'syn] t_t = object end
    let gcata_t _ _ _ = assert false
    let t =
        { GT.gcata = gcata_t
        ; GT.plugins = object
            method fmt fa fmt o = Format.fprintf fmt "<indent_map>"
            method gmap = Ident.Map.map
            method eq fa = phys_equal
            method compare fa l r =
              comparison_of_int @@
              Ident.Map.compare (fun x y -> int_of_comparison @@ fa x y) l r
        end
        ; GT.fix = (fun _ -> assert false)
        }
  end
  module Set = struct
    include Ident.Set

    class ['ia,'a,'sa, 'i, 'self, 'syn] t_t = object end
    let gcata_t _ _ _ = assert false
    let t =
        { GT.gcata = gcata_t
        ; GT.plugins = object
            method fmt fa fmt o = Format.fprintf fmt "<indent_set>"
            method gmap = Ident.Set.map
            method eq fa = phys_equal
            method compare l r =
              comparison_of_int @@
              Ident.Set.compare l r
        end
        ; GT.fix = (fun _ -> assert false)
        }
  end
end
module MyTypes = struct
  type type_expr = Types.type_expr

  let type_expr =
          { GT.gcata = (fun _ _ _ -> assert false)
          ; GT.plugins = object
              method fmt fmt = Format.fprintf fmt "%a" Printtyp.type_expr
              method gmap x = x
              method eq = Pervasives.(=)
              method compare a b = GT.compare GT.int a.Types.id b.Types.id
          end
          ; GT.fix = (fun _ -> assert false)
          }
end

let pp_longident () lident = Longident.flatten lident |> String.concat ~sep:"."

(*type logic_op = Conj | Disj
[@@deriving gt ~options:{ fmt; gmap; eq; compare }]*)
(* type bin_op = Plus | Minus
        | LT | LE | GT | GE | Eq
        | LOR
[@@deriving gt ~options:{ fmt; gmap; eq }] *)
(*type un_op = LNEG
[@@deriving gt ~options:{ fmt; gmap; eq; compare }]*)

(*type 'term pf = LogicBinOp of logic_op * 'term pf * 'term pf
              | Not of 'term pf
              | EQident of MyIdent.t * MyIdent.t
              | PFTrue
              | PFFalse
              | Term of 'term
[@@deriving gt ~options:{ fmt; gmap; eq; compare }]*)

(*type mem_repr = MemLeaf  of  int
              | MemBlock of { mem_tag: int; mem_sz: int; mem_cnt: mem_repr list }*)

type rec_flag = Asttypes.rec_flag = Nonrecursive | Recursive
  [@@deriving gt ~options:{ fmt; gmap; eq; compare }]

type builtin =
  | BiPlus
  | BiMinus
  | BiLT | BiLE | BiGT | BiGE
  (* logical operations *)
  | BiOr | BiAnd | BiNeg
  | BiStructEq
(*  | BiPhysEq*)
[@@deriving gt ~options:{ fmt; gmap; eq; compare }]


(* type   z = Z
type _ s = S : 'n -> 'n s

type ('size, 'a) vector =
  | Nil  :                                          (z, 'a) vector
  | Cons : ('a * ('oldsize, 'a) vector) -> ('oldsize s, 'a) vector *)

(* The index of memory location. Introduced because static names seems
 * to be not emough
 *)
type loc_id_t = GT.int [@@deriving gt ~options:{fmt; eq; gmap; compare}]

(* **)
type api = MyAPI of (rec_flag * term) MyIdent.Map.t
and term =
  (* Values specific to memory model *)
  (* int, bool and unit doesn't need types because we have them in Predef module *)
  | CInt  of GT.int
  | CBool of GT.bool
  | Unit
  | Lambda of { lam_argname: MyIdent.t GT.option
              ; lam_argtype: MyTypes.type_expr
              ; lam_api    : api
              ; lam_eff    : heap
              ; lam_body   : term
              ; lam_is_rec : GT.bool
              ; lam_typ    : MyTypes.type_expr
              }
  | Builtin of builtin
  | Link of loc_id_t * term * MyTypes.type_expr (*  maybe add readable name? *)


  (* Values specific for symbolic execution *)
  (* TODO: Lazy Instantiation contains a context heap, identifier and type of that identifier
    In case of reading from defined heap (when we know all concrete heaps) the None will be stored
    and it will be most common case. In more complex situation (Composition or Mutation of heap)
    Something will be stored there.
   *)
  | LI    of heap GT.option * MyIdent.t * MyTypes.type_expr
  | Ident of MyIdent.t * MyTypes.type_expr
  (* types for builtin values are predefined *)
  | Call    of term * term GT.list * MyTypes.type_expr
  | Union   of (term * term) GT.list

and defined_heap = (MyIdent.t * (MyTypes.type_expr * term)) GT.list
(* in general, defined heap is a mapping from identifiers to terms
   We use a list for simplicity and store a type near the key
*)
and heap =
  (** Heap should be a mapping from terms to terms (array access, for example)
    * but for fibonacci it doesn't matter
    *)
  (* TODO: it should be path instead of ident here *)
  | HDefined of defined_heap
  | HMerge of (term * heap) GT.list
  | HWrite of heap * MyIdent.t * term
  | HCmps of heap * heap
  | HCall of term * term GT.list
  (* Mutation: when we fill the holes in right heap by terms from left heap *)
  (* | HMutation of t * t  *)
[@@deriving gt ~options:{ fmt; eq; gmap; compare }]

type t = heap
[@@deriving gt ~options:{ fmt; eq; gmap; compare }]

module Defined = struct
  type t = defined_heap
  let filter = List.filter
  let add xs k v typ =  (k, (typ,v)) :: xs
  let hacky_fold ~cond ~f xs =
    List.fold_left xs ~init:([],[]) ~f:(fun (bad, acc) (k,(_typ,v)) ->
      if cond k v
      then (k::bad, add acc k (f k v) _typ)
      else (bad,    add acc k v       _typ)
    )
  let has_key xs k =
    try ignore (List.Assoc.find_exn xs k ~equal:MyIdent.equal); true
    with Not_found -> false

  let equal xs ys ~f =
    Int.equal (List.length xs) (List.length ys) &&
    List.for_all xs ~f:(fun (k,(_,v)) ->
      match List.Assoc.find ys ~equal:MyIdent.equal k with
      | None -> false
      | Some v2 -> f v v2
    )

  let map_values h ~f =
    List.map h (fun (ident, (typ, v)) -> (ident,(typ, f ident typ v)))
end

(* Pretty-printing boilerplate now *)

(*let fmt_unop fmt = function
| LNEG  -> Format.fprintf fmt "not "*)

let fmt_builtin fmt = function
  | BiPlus  -> Format.fprintf fmt "+"
  | BiMinus -> Format.fprintf fmt "-"
  | BiLT    -> Format.fprintf fmt "<"
  | BiGT    -> Format.fprintf fmt ">"
  | BiLE    -> Format.fprintf fmt "≤"
  | BiGE    -> Format.fprintf fmt "≥"
(*  | BiPhysEq    -> Format.fprintf fmt "=="*)
  | BiStructEq  -> Format.fprintf fmt "="
  | BiOr      -> Format.fprintf fmt "||"
  | BiAnd     -> Format.fprintf fmt "&&"
  | BiNeg     -> Format.fprintf fmt "not"


(*let fmt_logic_op fmt = function
  | Conj -> Format.fprintf fmt "∧"
  | Disj -> Format.fprintf fmt "∨"*)

(*
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
      (* | Not (Term (BinOp (LE,l,r,typ))) -> for_term fmt (BinOp (GT,l,r, typ))
      | Not (Term (BinOp (GT,l,r,typ))) -> for_term fmt (BinOp (LE,l,r, typ)) *)
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
      method eq    = pf.plugins#eq
    end
  }
*)
class ['extra_term] my_fmt_term
    ((for_api, for_defined_heap, for_heap, fself_term) as _mutuals_pack)
  =
  object
    inherit  ['extra_term] fmt_term_t_stub _mutuals_pack as super
    method! c_Lambda fmt _ argname _argtyp _api heap term flg _ =
      Format.fprintf fmt "(Lambda @[<v>{ ";
      Format.fprintf fmt "@[lam_argname@ =@ %a@]@," (GT.fmt GT.option (GT.fmt MyIdent.t)) argname;
      (* Format.fprintf fmt "@[; @[lam_api@ =@ %a@]@]@," for_api _x__091_; *)
      Format.fprintf fmt "@[; @[lam_eff@ =@ %a@]@]@,"  for_heap heap;
      Format.fprintf fmt "@[; @[lam_body@ =@ %a@]@]@," fself_term term;
      Format.fprintf fmt "@[; @[lam_is_rec@ =@ %b@]@]" flg;
      Format.fprintf fmt "})@]"
    method! c_Builtin fmt me op = super#c_Builtin fmt me op
    method! c_CBool    fmt _  b = Format.fprintf fmt "%b" b
    (* method! c_BinOp fmt _ op l r _typ =
      Format.fprintf fmt "@[(@,%a@ %a@,@ %a)@]"
        fself_term l
        fmt_binop op
        fself_term r
    method! c_UnOp fmt _ op arg _typ =
      Format.fprintf fmt "@[(@,%a@ %a)@]"
        fself_term arg
        fmt_unop op *)
    method! c_Link fmt _ idx t _ =
      Format.fprintf fmt "@[RefLocation@ _.%d@ to@ %a@]" idx fself_term t
    method! c_CInt fmt _ n = Format.fprintf fmt "%d" n
    method! c_Ident fmt _ ident _typ =
      Format.fprintf fmt "@[\"%a\"@]" (GT.fmt MyIdent.t) ident
    method! c_LI fmt _ h ident _typ =
      match h with
      | None -> Format.fprintf fmt "@[\"%a\"@]" (GT.fmt MyIdent.t) ident
      | Some h ->
           Format.fprintf fmt "LI@ @[(@,%a,@,@ \"%a\"@,)@]" for_heap h (GT.fmt MyIdent.t) ident
          (*Format.fprintf fmt "LI@ @[(@,...,@,@ \"%a\"@,)@]"  (GT.fmt MyIdent.t) ident*)
    method! c_Union fmt _ ps =
      (* TODO: normal printing *)
      Format.fprintf fmt "@[<hv>(Union@ ";
      GT.list.GT.plugins#fmt (fun fmt (l,r) ->
        Format.fprintf fmt "@[⦗@,@[%a@], @[%a@]@,⦘@]" fself_term l fself_term r
      ) fmt ps;
      Format.fprintf fmt ")@]";
      ()
    method c_Call fmt _ f args _typ =
      match f with
      | Ident (id, typ) ->
          Format.fprintf fmt "Call@ @[@,%a,@,@ (%a@,)@]" fself_term f (GT.fmt GT.list fself_term) args
          | Builtin BiStructEq ->
              assert (List.length args = 2);
              let l = List.hd_exn args in
              let r = List.nth_exn args 1 in
              Format.fprintf fmt "@[(%a@ =@ %a)@]" fself_term l fself_term r
(*
      | Builtin BiPhysEq ->
        assert (List.length args = 2);
        let l = List.hd_exn args in
        let r = List.nth_exn args 1 in
        Format.fprintf fmt "@[(%a@ ==@ %a)@]" fself_term l fself_term r
        *)
      | Builtin BiLE ->
          assert (List.length args = 2);
          let l = List.hd_exn args in
          let r = List.nth_exn args 1 in
          Format.fprintf fmt "@[(%a@ ≤@ %a)@]" fself_term l fself_term r
      | Builtin (BiAnd as op) ->
          assert (List.length args > 0);
          Format.fprintf fmt "@[(";
          List.iteri args ~f:(fun i t ->
            if i>0 then Format.fprintf fmt "@ %a@ " fmt_builtin op;
            fself_term fmt t
          );
          Format.fprintf fmt ")@]";
      | Builtin BiNeg ->
          assert (List.length args = 1);
          Format.fprintf fmt "@[¬(%a)@]" fself_term (List.hd_exn args)
      | _ ->
          Format.fprintf fmt "Call@ @[@,%a,@,@ (%a@,)@]" fself_term f (GT.fmt GT.list fself_term) args
  end

let hack_rec_flg fmt = function
  | Recursive    -> Format.fprintf fmt "|rec↦"
  | Nonrecursive ->  Format.fprintf fmt "↦"

class ['extra_api] my_fmt_api
    ((for_api, (for_defined_heap: _ -> defined_heap -> _), for_heap, for_term) as _mutuals_pack)
  =
  object
    inherit  ['extra_api] fmt_api_t_stub _mutuals_pack

    method! c_MyAPI fmt _ mapa =
      if Ident.Map.is_empty mapa
      then Format.fprintf fmt "[]"
      else
        let (khead,(flg,thead)) = Ident.Map.min_binding mapa in
        Format.pp_open_vbox fmt 0;
        (* Format.fprintf fmt   "@[<hov>[@ %a@ %a@ %a@]@]@,"
            (GT.fmt MyIdent.t) khead
            hack_rec_flg flg
            for_term thead; *)
        mapa |> Ident.Map.iter (fun k (flg,t) ->
            Format.fprintf fmt "@[<h>%c@ @[%a@ %a@ %a@]@]@,"
              (if MyIdent.equal k khead then '[' else ';')
              (GT.fmt MyIdent.t) k
              hack_rec_flg flg
              for_term t
          );
          Format.fprintf fmt "]";
          Format.pp_close_box fmt ()

  end

class ['extra_defined_heap] my_fmt_defined_heap
    ((for_api, (for_defined_heap: _ -> defined_heap -> _), for_heap, for_term) as _mutuals_pack)
  =
  object
    inherit  [Format.formatter,'extra_defined_heap,unit] defined_heap_t
    constraint 'extra_defined_heap = defined_heap

    method c_Nil fmt _ = Format.fprintf fmt "@[ε@]"
    method c_Cons fmt _ ((hi,(_htyp,hterm)) as head) (xs: defined_heap) =
      let (_: (MyIdent.t * (MyTypes.type_expr * term)) ) = head in
      Format.open_hvbox 0;
      (* Format.fprintf fmt   "\x1b[31m"; *)
      Format.fprintf fmt   "@[<hov>⟦ @[⦗%a,@ %a⦘@]@]" (GT.fmt MyIdent.t) hi for_term hterm;
      List.iter xs ~f:(fun (ident,(_typ,term)) ->
        Format.fprintf fmt "@[<hov>; @[⦗%a,@ %a⦘@]@]" (GT.fmt MyIdent.t) ident for_term term
      );
(*      Format.fprintf fmt   "\x1b[31m";*)
      Format.fprintf fmt "⟧";
(*      Format.fprintf fmt "\x1b[39;49m";*)
      Format.close_box ();   (* closing hvbox *)
      ()

  end

class ['extra_t] my_fmt_heap ((for_api, (for_defined_heap: _ -> defined_heap -> _), for_heap, for_term) as _mutuals_pack)
  =
  object
    inherit  ['extra_t] fmt_heap_t_stub _mutuals_pack

    method! c_HDefined fmt _ xs = for_defined_heap fmt xs

    method! c_HCmps fmt _ l r =
      Format.fprintf fmt "@[(%a@ ∘@ %a)@]" for_heap l for_heap r
    method c_HCall fmt _ f args =
      Format.fprintf fmt "@[(RecApp@ @[%a@ (%a)@])@]"
        for_term f
        (GT.fmt GT.list for_term) args
    method c_HMerge fmt _ pfs =
      Format.fprintf fmt "@[<h>(HMerge@ ";
      let () = match pfs with
        | [] -> Format.fprintf fmt "[]"
        | x::xs ->
          Format.fprintf fmt "@[<v>";
          let f fmt (g,h) = Format.fprintf fmt "(%a, %a)" for_term g for_heap h in
          Format.fprintf fmt   "@[[ %a@]" f x;
          List.iter xs ~f:(fun p -> Format.fprintf fmt "@,@[; @,%a@]@," f p);
          Format.fprintf fmt "]@]"
      in
      Format.fprintf fmt ")@]"
  end

let fmt_api_0          = new my_fmt_api
let fmt_defined_heap_0 = new my_fmt_defined_heap
let fmt_heap_0         = new my_fmt_heap
let fmt_term_0         = new my_fmt_term

let fmt_api eta =
  let (f, _, _, _) =
    fix_api fmt_api_0 fmt_defined_heap_0 fmt_heap_0 fmt_term_0 in
  f eta
let fmt_defined_heap eta =
  let (_, f, _, _) =
    fix_api fmt_api_0 fmt_defined_heap_0 fmt_heap_0 fmt_term_0 in
  f eta
let fmt_heap eta =
  let (_, _, f, _) =
    fix_api fmt_api_0 fmt_defined_heap_0 fmt_heap_0 fmt_term_0 in
  f eta
let fmt_term eta =
  let (_, _, _, f) =
    fix_api fmt_api_0 fmt_defined_heap_0 fmt_heap_0 fmt_term_0 in
  f eta

let api = {
    GT.gcata = gcata_api;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_api end)
  }
let t = {
    GT.gcata = gcata_t;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_t end)
  }
let term =  {
    GT.gcata = gcata_term;
    GT.fix = fix_api;
    GT.plugins = object
      method fmt = fmt_term
      method eq  = term.plugins#eq
      method gmap  = term.plugins#gmap
    end
  }
let defined_heap = {
    GT.gcata = gcata_defined_heap;
    GT.fix = fix_api;
    GT.plugins =
      (object
         method compare = compare_defined_heap
         method gmap = gmap_defined_heap
         method eq = eq_defined_heap
         method fmt = fmt_defined_heap
       end)
  }
let heap = {
    GT.gcata = gcata_heap;
    GT.fix = fix_api;
    GT.plugins = object
      method fmt     = fmt_heap
      method eq      = eq_heap
      method gmap    = gmap_heap
      method compare = compare_heap
    end
  }

(* End of Pretty-printing boilerplate *)
