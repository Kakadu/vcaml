let failwiths fmt = Format.kprintf failwith fmt

module MyIdent = struct
  type longident = Longident.t =
    | Lident of GT.string
    | Ldot of longident * GT.string
    | Lapply of longident * longident
    [@@deriving gt ~options:{ fmt }]

  type t = Ident.t

  let to_string ident = Ident.unique_name ident
   (* Sexplib.Sexp.to_string_hum @@ sexp_of_t ident *)
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
and term = LI of heap GT.option * MyIdent.t
          | CInt of GT.int
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
and t = HAssoc of (MyIdent.t * term) GT.list
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
    method! c_BinOp inh___079_ _ _x__080_ _x__081_ _x__082_ =
      Format.fprintf inh___079_ "@[(@,%a@ %a@,@ %a)@]"
        fself_term _x__081_
        fmt_op _x__080_
        fself_term _x__082_
    method! c_CInt fmt _ = Format.fprintf fmt "%d"
    method! c_LI fmt _ h ident =
      match h with
      | None -> Format.fprintf fmt "@[(LI \"%a\")@]" (GT.fmt MyIdent.t ) ident
      | Some h ->
          Format.fprintf fmt "LI@ @[(@,%a,@,@ %a@,)@]"     for_heap h
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
      let f = fun fmt (l,r) ->
        Format.fprintf fmt "@[%a@ ↦@ %a@]" (GT.fmt MyIdent.t) l for_term r
      in
      GT.list.GT.plugins#fmt f fmt xs
  end

class ['extra_t] my_fmt_t ((for_api, for_pf, fself_t, for_term, for_heap)
                                 as _mutuals_pack)
  =
  object
    inherit  ['extra_t] fmt_t_t_stub _mutuals_pack

    method! c_HAssoc fmt _ xs =
      Format.fprintf fmt "⟦";
      List.iter xs ~f:(fun (ident,term) ->
        Format.fprintf fmt "@[⦗@,%a, %a@,⦘@]" (GT.fmt MyIdent.t) ident for_term term
      );
      Format.fprintf fmt "⟧"
    method! c_HCmps fmt _ l r =
      Format.fprintf fmt "@[(%a@ ∘@ %a)@]" for_heap l for_heap r
    method c_HCall inh___070_ _ _x__071_ _x__072_ =
      Format.fprintf inh___070_ "(HCall@ @[(@,%a,@,@ %a@,)@])" for_term
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
    method! c_LogicBinOp inh___050_ _ _x__051_ _x__052_ _x__053_ =
      Format.fprintf inh___050_ "@[(@,%a,@,@ %a@, %a@,)@]"
        fself_pf _x__052_
        fmt_logic_op _x__051_
        fself_pf _x__053_
    method! c_Not inh___054_ _ _x__055_ =
      Format.fprintf inh___054_ "(¬%a)" fself_pf _x__055_
    method! c_EQident inh___056_ _ _x__057_ _x__058_ =
      Format.fprintf inh___056_ "@[(%a@ =@ %a)@]"
        (GT.fmt MyIdent.t ) _x__057_
        (GT.fmt MyIdent.t ) _x__058_
    method! c_PFTrue inh___059_ _ = Format.fprintf inh___059_ "TRUE"
    method! c_PFFalse inh___060_ _ = Format.fprintf inh___060_ "FALSE"
    method! c_Term inh___061_ _ _x__062_ =
      Format.fprintf inh___061_ "@[(Term@ (%a))@]" for_term _x__062_
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
let pp_term () t =
  Format.asprintf "%a" term.GT.plugins#fmt t

let pp_heap () h = Format.asprintf "%a" heap.GT.plugins#fmt h

let fold_defined ~f ~init = List.fold_left ~init ~f
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
let pf_eq id1 id2 = EQident (id1, id2)
let pf_conj_list = function
  | [] -> PFTrue
  | h::hs -> List.fold_left ~init:h hs ~f:(pf_binop Conj)
let hempty : t = HEmpty
let hsingle name el : t = HAssoc [(name,el)]
let hmerge2 g1 h1 g2 h2 = HMerge [(g1,h1); (g2,h2)]
let hmerge_list xs = HMerge xs
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
                 |> Option.value_map ~f:(fun t -> t) ~default
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
  | PFTrue -> PFTrue
  | PFFalse -> PFFalse
  | LogicBinOp (op, l, r) -> LogicBinOp (op, fat_dot_pf heap l, fat_dot_pf heap r)
  | Not pf -> Not (fat_dot_pf heap pf)
  | Term t -> Term (fat_dot heap t)
  | EQident (l,r) -> failwiths "not implemented %s %d" __FILE__ __LINE__
and simplify_pf pf = pf

let rec hdot_defined hs term =
  match term with
  | LI (None, ident) -> read_ident_defined hs ident
  | LI (Some _, ident) -> failwiths "not implemented %s %d" __FILE__ __LINE__
  | BinOp (op, l, r) -> BinOp (op, hdot_defined hs l, hdot_defined hs r)
  | Unit
  | CInt _ -> term
  | Union us     -> assert false
  | Call (f,arg) ->
      Format.eprintf "TODO: not implemented %s %d\n%!" __FILE__ __LINE__;
      Call (hdot_defined hs f, hdot_defined hs arg)
  | Lambda _ ->
      Format.eprintf "TODO: not implemented %s %d\n%!" __FILE__ __LINE__;
      term

and read_ident_defined hs ident =
  if List.Assoc.mem hs ident ~equal:MyIdent.equal
  then List.Assoc.find_exn hs ident ~equal:MyIdent.equal
  else
    (* We should return UNION here *)
    let positives = List.map hs ~f:(fun (k,v) ->
      (pf_eq k ident, v)
    )
    in
    let neg = pf_conj_list @@ List.map hs ~f:(fun (k,_) -> pf_not @@ pf_eq k ident) in
    union @@ (neg, li ident) :: positives

let write_ident_defined hs ident (newval: term) : heap =
  let positives = List.map hs ~f:(fun (k,v) ->
      let newh = List.filter hs ~f:(fun (i,_) -> not (MyIdent.equal i k)) in
      let newh = (ident, newval) :: newh in
      (pf_eq k ident, HAssoc newh)
  )
  in
  let neg = pf_conj_list @@ List.map hs ~f:(fun (k,_) -> pf_not @@ pf_eq k ident) in
  HMerge ( (neg, HAssoc ((ident, newval) :: hs)) :: positives)

(**
 *
 *)
let hcmps_defined ms ns =
  (* TODO: fancy algorithm here *)
  let rec mutate ns a = a in
  fold_defined ns ~init:[] ~f:(fun acc (k,v) ->
    let a = fat_dot (HAssoc ms) v in
    (k, mutate ns a) :: acc
  )


(** Heap operations *)
let hcmps : t -> t -> t = fun a b ->
  Format.eprintf "calling hcmps of\n%!";
  Format.eprintf "\t%s\n%!" (pp_heap () a);
  Format.eprintf "\t%s\n%!" (pp_heap () b);
  match (a,b) with
  | (HEmpty,b) -> b
  | (a,HEmpty) -> a
  | (HAssoc xs, HAssoc ys) -> HAssoc (hcmps_defined xs  ys)
  | _ -> HCmps (a,b)

let rec heap_subst heap lident new_term =
  Format.eprintf "heap_subst not implemented\n%!";
  heap
and term_subst term lident new_term =
  Format.eprintf "heap_subst not implemented\n%!";
  term

module Api = struct
  type t = api * MyIdent.t list
  let empty = ([],[])

  (* let fold_api ~f ~init xs = List.fold_left ~f ~init xs *)
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
