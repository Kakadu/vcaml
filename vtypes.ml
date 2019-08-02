let failwiths fmt = Format.kprintf failwith fmt

module MyIdent = struct
  type longident = Longident.t =
    | Lident of GT.string
    | Ldot of longident * GT.string
    | Lapply of longident * longident
    [@@deriving gt ~options:{ fmt }]

  type t = Ident.t

  let to_string ident = Ident.unique_name ident
  let sexp_of_t ident  = to_string ident |> Sexplib.Std.sexp_of_string
  let pp_string () = to_string
  let equal = Ident.equal

  let t = { GT.gcata = (fun _ _ _ -> assert false)
          ; GT.plugins = object
              method fmt fmt o = Format.fprintf fmt "%s" (Ident.unique_name o)
          end
          ; GT.fix = (fun _ -> assert false)
          }
end

(* type cre_mode = Assign | Const [@@deriving gt ~options:{ fmt }] *)
let pp_longident () lident = Longident.flatten lident |> String.concat ~sep:"."

type logic_op = Conj | Disj [@@deriving gt ~options:{ fmt }]
type op = | Plus | Minus | LT | LE | GT | GE | Eq [@@deriving gt ~options:{ fmt }]

type api = (MyIdent.t * term) GT.list
and term  = LI of heap GT.option * MyIdent.t
          | CInt of GT.int
          | CBool of GT.bool
          | BinOp of op * term * term
          | Unit
          | Call of term * term
          | Union of (pf * term) GT.list
          | Lambda of { lam_argname: MyIdent.t GT.option
                      ; lam_api   : api
                      ; lam_eff   : heap
                      ; lam_body  : term
                      ; lam_is_rec: GT.bool
                      }

(* TODO: it should be path here *)
and t = HDefined of (MyIdent.t * term) GT.list
        (* Heap should be a mapping from terms to terms (array access, for example)
         * but for fibonacci it doesn't matter
         *)
      | HMerge of (pf * t) GT.list
      | HCmps of heap * heap
      | HCall of term * term
      | HEmpty

and pf  = LogicBinOp of logic_op * pf * pf
        | Not of pf
        | EQident of MyIdent.t * MyIdent.t
        | PFTrue
        | PFFalse
        | Term of term
and heap = t [@@deriving gt ~options:{ fmt }]

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

class ['extra_term] my_fmt_term
    ((for_api, for_pf, for_t, fself_term,for_heap) as _mutuals_pack)
  =
  object
    inherit  ['extra_term] fmt_term_t_stub _mutuals_pack
    method! c_Lambda fmt _ _x__090_ _x__091_ _x__092_ _x__093_ _x__094_ =
      Format.fprintf fmt "(Lambda @[<v>{ ";
      Format.fprintf fmt "@[lam_argname@ =@ %a@]@," (GT.fmt GT.option (GT.fmt MyIdent.t)) _x__090_;
      Format.fprintf fmt "@[; @[lam_api@ =@ %a@]@]@," for_api _x__091_;
      Format.fprintf fmt "@[; @[lam_eff@ =@ %a@]@]@,"  for_heap _x__092_;
      Format.fprintf fmt "@[; @[lam_body@ =@ %a@]@]@," fself_term _x__093_;
      Format.fprintf fmt "@[; @[lam_is_rec@ =@ %b@]@]" _x__094_;
      Format.fprintf fmt "})@]"
    method! c_BinOp inh___079_ _ op l r =
      Format.fprintf inh___079_ "@[(@,%a@ %a@,@ %a)@]"
        fself_term l
        fmt_op op
        fself_term r
    method! c_CInt fmt _ = Format.fprintf fmt "%d"
    method! c_LI fmt _ h ident =
      match h with
      | None -> Format.fprintf fmt "@[\"%a\"@]" (GT.fmt MyIdent.t) ident
      | Some h ->
          Format.fprintf fmt "LI@ @[(@,%a,@,@ \"%a\"@,)@]" for_heap h
            (GT.fmt MyIdent.t) ident
    method! c_Union fmt _ ps =
      (* TODO: normal printing *)
      Format.fprintf fmt "@[(Union@ ";
      GT.list.GT.plugins#fmt (fun fmt (l,r) ->
        Format.fprintf fmt "@[⦗@,@[%a@], @[%a@]@,⦘@]" for_pf l fself_term r
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
  end

class ['extra_api] my_fmt_api
    ((for_api, for_pf, for_t, for_term,for_heap) as _mutuals_pack)
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
      let f fmt (l,r) =
        Format.fprintf fmt "@[%a@ ↦@ %a@]" (GT.fmt MyIdent.t) l for_term r
      in
      GT.list.GT.plugins#fmt f fmt xs
  end

class ['extra_t] my_fmt_t ((for_api, for_pf, fself_t, for_term, for_heap)
                                 as _mutuals_pack)
  =
  object
    inherit  ['extra_t] fmt_t_t_stub _mutuals_pack

    method! c_HDefined fmt _ xs =
      Format.fprintf fmt "⟦";
      List.iter xs ~f:(fun (ident,term) ->
        Format.fprintf fmt "@[⦗@,%a, %a@,⦘@]" (GT.fmt MyIdent.t) ident for_term term
      );
      Format.fprintf fmt "⟧"
    method! c_HCmps fmt _ l r =
      Format.fprintf fmt "@[(%a@ ∘@ %a)@]" for_heap l for_heap r
    method c_HCall inh___070_ _ _x__071_ _x__072_ =
      Format.fprintf inh___070_ "(RecApp@ @[(@,%a,@,@ %a@,)@])" for_term
        _x__071_ for_term _x__072_
    method c_HMerge fmt _ _x__066_ =
      Format.fprintf fmt "@[(HMerge@ @[";
      Format.fprintf fmt "%a" (GT.fmt GT.list (GT.fmt GT.tuple2 for_pf fself_t)) _x__066_;
      Format.fprintf fmt "@])@]"

    method! c_HEmpty inh___073_ _ = Format.fprintf inh___073_ "ε"
  end

class ['extra_pf] my_fmt_pf
        ((for_api, fself_pf, for_t, for_term, for_heap) as _mutuals_pack)
  =
  object
    inherit ['extra_pf] fmt_pf_t_stub _mutuals_pack
    method! c_LogicBinOp fmt _ _x__051_ _x__052_ _x__053_ =
      Format.fprintf fmt "@[(@,%a,@,@ %a@, %a@,)@]"
        fself_pf _x__052_
        fmt_logic_op _x__051_
        fself_pf _x__053_
    method! c_Not fmt _ _x__055_ =
      Format.fprintf fmt "¬%a" fself_pf _x__055_
    method! c_EQident fmt _ _x__057_ _x__058_ =
      Format.fprintf fmt "@[(%a@ =@ %a)@]"
        (GT.fmt MyIdent.t ) _x__057_
        (GT.fmt MyIdent.t ) _x__058_
    method! c_PFTrue fmt _ = Format.fprintf fmt "TRUE"
    method! c_PFFalse fmt _ = Format.fprintf fmt "FALSE"
    method! c_Term fmt _ _x__062_ =
      Format.fprintf fmt "@[%a@]" for_term _x__062_
  end
let fmt_term_0 = new my_fmt_term
let fmt_pf_0 = new my_fmt_pf
let fmt_api_0 = new my_fmt_api
let fmt_t_0 = new my_fmt_t
let fmt_heap_0 = fmt_t_0
let fmt_api eta =
  let (f, _, _, _, _) =
    fix_api fmt_api_0 fmt_pf_0 fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_pf eta =
  let (_, f, _, _, _) =
    fix_api fmt_api_0 fmt_pf_0 fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_t eta =
  let (_, _, f, _, _) =
    fix_api fmt_api_0 fmt_pf_0 fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_term eta =
  let (_, _, _, f, _) =
    fix_api fmt_api_0 fmt_pf_0 fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta
let fmt_heap eta =
  let (_, _, _, _, f) =
    fix_api fmt_api_0 fmt_pf_0 fmt_t_0 fmt_term_0 fmt_heap_0 in
  f eta

let api = {
    GT.gcata = gcata_api;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_api end)
  }
let _ = api
let pf = {
    GT.gcata = gcata_pf;
    GT.fix = fix_api;
    GT.plugins = (object method fmt = fmt_pf end)
  }
let _ = pf
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
    GT.plugins = (object method fmt = fmt_heap end)
  }

(* End of Pretty-printing boilerplate *)
