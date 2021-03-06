open Vtypes
open Vpredef
open Vutils

let pp_term () t =
  Format.asprintf "%a" term.GT.plugins#fmt t

let pp_heap () (h: heap) = Format.asprintf "%a" (GT.fmt heap) h

let fold_defined ~f ~init = List.fold_left ~init ~f

let rec type_of_term root =
(*  let wrap desc = { Types.level = 0; scope = None; id=0; desc } in*)
  match root with
  | Unreachable -> None
  | Union [] -> None
  | Union ((_,t)::_) -> type_of_term t
  | Reference (_, info) -> si_typ info
  | CInt _  -> Some Predef.type_int
  | CBool _ -> Some Predef.type_bool
  | Unit    -> Some Predef.type_unit
  | LI (_,_,t)
  | Ident (_,t)
  (* | BinOp (_,_,_,t) *)
  | Lambda {lam_typ = t}
  | Call (_,_,t) ->  si_typ t
  | Builtin b -> match b with
(*  | BiPhysEq*)
  | BiStructEq -> Some Vpredef.type_eq
  | BiMinus
  | BiPlus -> Some Vpredef.type_int_arith
  | BiLT | BiLE | BiGE
  | BiGT -> Some Vpredef.type_int_cmp
  | BiOr
  | BiAnd -> Some Vpredef.logical_and
  | BiNeg -> Some Vpredef.logical_neg

  (* | _ -> failwiths "Not implemented %s %d" __FILE__ __LINE__ *)

module Api = struct
  type ident_info = { ii_unique: bool }
  type t =
    { api: api
    ; pending:  heap_loc list
    ; ii:      ident_info HeapLocMap.t
    }
  let empty: t = { api = MyAPI HeapLocMap.empty; pending = []; ii = HeapLocMap.empty }

  (* let fold_api ~f ~init xs = List.fold_left ~f ~init xs *)
  let add ({api = MyAPI api } as a) key data =
    { a with api = MyAPI (Map.add_exn api ~key ~data ) }

  let add_pending       api new_ = {api with pending = new_ :: api.pending }
  let add_pending_ident api new_ = add_pending api (LoIdent new_)

  let remove_pending_exn api el =
    { api with pending = List.filter api.pending ~f:(GT.eq heap_loc el) }

  let is_pending { pending } loc : bool =
    List.exists pending ~f:(GT.eq heap_loc loc)
  let is_pending_ident xs id = is_pending xs (LoIdent id)

  let is_recursive_exn { api = MyAPI api; pending } ident =
    List.mem pending ident ~equal:(GT.eq heap_loc) ||
    match Map.find_exn api ident with
    | (Recursive,_,_) -> true
    | (Nonrecursive,_,_) -> false

  let is_recursive_ident_exn xs ident = is_recursive_exn xs (LoIdent ident)

  let find_exn : t -> heap_loc -> api_item = fun { api = MyAPI api } ident ->
    Map.find_exn api ident
  let find_ident_exn : t -> MyIdent.t -> api_item = fun { api = MyAPI api } ident ->
    Map.find_exn api (LoIdent ident)

    (* List.find_map_exn api ~f:(fun (k,flg,t) ->
      if MyIdent.equal ident k
      then Some (flg,t)
      else None
    ) *)
    (* List.find_exn api ~f:(fun (k,flg,t) -> )
    List.Assoc.find_exn ~equal:MyIdent.equal api ident *)
  let find_ident_li : t -> MyIdent.t -> MyTypes.type_expr -> term = fun api ident typ ->
    try let (_,t,_) = find_ident_exn api ident in
        t
    with Not_found ->
        let sinfo = make_sinfo ~typ () in
        LI (None, Ident (ident, sinfo), sinfo)

  let mark_unique api id =
    { api with ii = Map.add_exn ~key:id ~data:{ ii_unique = true } api.ii }
end

(** Simplification *)

(* let eval_binop = function
  | Plus  -> (fun x y -> CInt  (x+y))
  | Minus -> (fun x y -> CInt  (x-y))
  | LT    -> (fun x y -> CBool (x<y))
  | LE    -> (fun x y -> CBool (x<=y))
  | GT    -> (fun x y -> CBool (x>y))
  | GE    -> (fun x y -> CBool (x>=y))
  | Eq    -> (fun x y -> CBool (x=y)) *)
(*
let eval_builtin = function
  | BiPlus  -> (fun x y -> CInt  (x+y))
  | BiMinus -> (fun x y -> CInt  (x-y))
  | BiLT    -> (fun x y -> CBool (x<y))
  | BiLE    -> (fun x y -> CBool (x<=y))
  | BiGT    -> (fun x y -> CBool (x>y))
  | BiGE    -> (fun x y -> CBool (x>=y))
  | BiEq    -> (fun x y -> CBool (x=y))
  | BiOR    -> (fun x y -> CBool (x || y)) *)

let simplify_term t =
  let rec helper = function
  | Call (Builtin (BiPlus as op), [l;r], _typ2) ->
      wrapInt l r
        ~ok:(fun m n -> CInt (m+n))
        ~fail:(fun l r -> Call (Builtin op, [l;r], _typ2) )
  | Call (Builtin (BiMinus as op), [l;r], _typ2) ->
      wrapInt l r
        ~ok:(fun m n -> CInt (m-n))
        ~fail:(fun l r -> Call (Builtin op, [l;r], _typ2) )
  | term -> term
  and wrapInt l r ~ok ~fail =
    match (helper l, helper r) with
      | (CInt n, CInt m) -> ok n m
      | (l,r) -> fail l r
  in
  helper t

(*
let rec simplify_pf = function
  | Not ph -> begin
      match simplify_pf ph with
      | EQident (l,r) when Ident.equal l r -> PFFalse
      | Not ph  -> ph
      | PFTrue  -> PFFalse
      | PFFalse -> PFTrue
      | ph      -> Not ph
    end
  | LogicBinOp (Conj, PFFalse, _)
  | LogicBinOp (Conj, _, PFFalse) -> PFFalse
  | LogicBinOp (Disj, PFTrue, _)
  | LogicBinOp (Disj, _, PFTrue) -> PFTrue
  | EQident (l,r) when Ident.equal l r -> PFTrue
  | ph -> ph
*)
(*
let simplify_guards gs =
  let exception QQQ in
  List.filter_map gs ~f:(fun (ph, term) ->
    match simplify_pf ph with
    | PFTrue -> Some (PFTrue, simplify_term term)
    | PFFalse -> None
    | pf -> Some (pf, simplify_term term)
  )
*)

let next_link_id : unit -> loc_id_t =
  let c = ref 400 in
  fun () ->
    Int.incr c;
    !c

(** Term operations *)

let cint n = CInt n
let cbool b = CBool b
let cunit = Unit
let lambda lam_is_rec lam_argname ~arg_type lam_api lam_eff lam_body lam_typ =
  simplify_term @@ Lambda
    { lam_argname
    ; lam_argtype=arg_type
    ; lam_api; lam_eff; lam_body; lam_is_rec; lam_typ
    }
let ident longident typ = Ident (longident, typ)
let li ?heap loc info = LI (heap, loc, info)
let li_ident ?heap longident typ = LI (heap, ident longident typ, typ)

let link id typ = Reference (id, typ)
let new_link typ =
  let id = next_link_id() in
  (id, link id typ)

let term_biAnd : term = Builtin BiAnd
let conj a b term_typ =
  Call (term_biAnd, [a;b], make_sinfo ~typ:Predef.type_bool ())


let binop op a b typ = simplify_term @@ Call (op, [a;b], typ)
let unop  op arg typ = simplify_term @@ Call (op, [arg], typ)

let boolean b = CBool b
let builtin op = Builtin op

let are_two_links = function
  | Reference (_,_), Reference(_,_) -> true
  | _ -> false
let link_and_ident = function
  | Reference (_,_), Ident(_,_) -> true
  | Ident(_,_), Reference (_,_) -> true
  | _ -> false
let same_idents = function
  | Ident (x,_), Ident(y,_) when GT.eq MyIdent.t x y -> true
  | LI(_,x,_), LI(_,y,_) when GT.eq term x y -> true   (* TODO: performance *)
  | _ -> false


let call_deoptimized fexpr args typ =
  (* TODO: add hash consing here *)
  Call (fexpr, args, typ)

let pf_eq t1 t2 =
  (* if (String.equal (MyIdent.to_string id1) "loop_1637" &&
      String.equal (MyIdent.to_string id2) "ndx_1003"
    )
  then assert false; *)
  if are_two_links (t1,t2) || link_and_ident (t1,t2)
  then boolean false
  else if same_idents (t1,t2)
  then boolean true
  else
      (* TODO: simplify arguments *)
      call_deoptimized (Builtin BiStructEq) [ t1; t2 ] (make_sinfo ~typ:Predef.type_bool ())

let tands ts =
  let ifempty ~k = function
  | [] -> boolean false
  | xs -> k xs
  in
  ifempty ts ~k:(fun ts ->
      List.foldk ts ~init:[]
        ~f:(fun acc x xs k ->
          match x with
          | CBool false as rez -> rez
          | CBool true -> k acc
          | _ -> k (x::acc)
        )
        ~finish:(ifempty ~k:(fun xs -> call_deoptimized (Builtin BiAnd) xs (make_sinfo ~typ:Predef.type_bool ())) )
  )

let tand t1 t2 = tands [t1; t2]
  (*
  match t1,t2 with
  | CBool false, _
  | _, CBool false -> t1
  | CBool true,t2
  | t2,CBool true -> t2
  | _   ->
      call_deoptimized (Builtin BiAnd) [t1; t2] Predef.type_bool*)

let neg_deoptimized t = call_deoptimized (Builtin BiNeg) [ t ] (make_sinfo ~typ:Predef.type_bool ())
let pf_not t =
  match t with
  | Call (Builtin BiStructEq, [ t1; t2 ], _) when are_two_links (t1,t2) ->  boolean true
  | Call (Builtin BiStructEq, [ t1; t2 ], _) when same_idents   (t1,t2) ->  boolean true
  | CBool true -> boolean false
  | CBool false -> boolean true
  | _ -> neg_deoptimized t

let union_deoptimized gts = Union gts

let rec union xs =
  (* Printexc.print_raw_backtrace stdout (Printexc.get_callstack 2); *)
  (* TODO: optimize Union [ ⦗("n_1635" < 0), x⦘; ⦗¬("n_1635" < 0), x⦘] *)
  (*match simplify_guards xs with*)
  match xs with
  | [ (CBool  true, t) ] -> t
  | []                   -> Unreachable
  | (CBool false, _) :: us -> union us
  | [ (g1,x); (g2,y) ] when (GT.eq Vtypes.term x y)
          && (GT.eq Vtypes.term g1 (pf_not g2) || GT.eq Vtypes.term g2 (pf_not g1)  )
          -> x
  (*| [ (g1,x); (g2,y)] when (GT.eq Vtypes.term x y)
        && (GT.eq Vtypes.term g1 (Not g2) || GT.eq Vtypes.term g2 (Not g1)  )
      -> x*)
  | xs ->
      let reduced =
        List.concat_map xs ~f:(fun (g,t) ->
          match t with
          | Union inners -> List.map inners ~f:(fun (k,v) ->
              let new_g = tand g k in
              (simplify_term new_g, v)
            )
          | _ -> [ (g,t) ]
          )
      in
      union_deoptimized @@ List.dedup_and_sort reduced
        ~compare:(fun (a,_) (b,_) -> int_of_comparison @@ GT.compare term a b)
let union2 g1 t1 g2 t2 = union [(g1,t1); (g2,t2)]
(*let builtin op typ = Builtin (op, typ)*)

let is_empty_union = function
  | Union [] -> true
  | _ -> false

(** Propositonal formula operations *)
(*
let pf_term el = Term el
let pf_not pf = simplify_pf @@ Not pf
let pf_binop op f1 f2 = simplify_pf @@ LogicBinOp (op, f1, f2)
*)

let call fexpr args typ =
  (* Format.eprintf "constructing call of '%s' to '%s'\n" (pp_term () fexpr)  (pp_term () arg); *)
  match args with
  | [] -> fexpr
  | args ->
      match fexpr,args with
      | (Builtin BiStructEq, [l;r]) -> pf_eq l r
      | (Builtin BiAnd, [l;r]) -> tand l r
      | (Builtin BiNeg, [x])   -> pf_not x
      | _ -> call_deoptimized fexpr args typ

let sinfo_bool = make_sinfo ~typ:Predef.type_bool ()
let pf_neq t1 t2 =
  call (builtin BiNeg) [ call (builtin BiStructEq) [t1; t2] sinfo_bool ] sinfo_bool

let pf_binop op f1 f2 typ = call (Builtin op) [f1; f2] typ
(*let pf_conj l r = pf_binop BiAnd l r Vpredef.type_bool*)

let pf_conj_list = function
  | [] -> CBool true
  | h::hs -> List.fold_left ~init:h hs ~f:tand

(*let pf_neq t1 t2 =
  pf_not @@ call_deoptimized (Builtin BiStructEq) [ t1; t2 ] Vpredef.type_bool*)

(*
let pf_neq id1 id2 = simplify_pf @@ pf_not @@ EQident (id1, id2)
let pf_conj_list = function
  | [] -> PFTrue
  | h::hs -> List.fold_left ~init:h hs ~f:(pf_binop Conj)

*)

(** Heap construction *)
let his_empty = function
  | HDefined [] -> true
  | _ -> false
let hempty : heap = HDefined []
let hdefined xs = HDefined xs
let rec hsingle name el typ : t =
  match el with
  | Union gs -> HMerge (List.map gs ~f:(fun (gu,term) -> (gu, hsingle name term typ)))
  | _ -> hdefined [(name,(typ,el))]
let hmerge2 g1 h1 g2 h2 = HMerge [(g1,h1); (g2,h2)]
let hmerge_list xs = HMerge xs
let hcall f x = HCall (f,x)

(*
(* * The main heap access function a.k.a. READ
let rec hfind_exn (heap: heap) ident : term =
  match hfind heap ident with
  | None -> raise Not_found
  | Some ans -> ans
and hfind heap ident =
  match heap with
  | HDefined xs -> List.Assoc.find xs ~equal:Longident.equal ident
  | HEmpty -> None
  | HMerge hs ->
      List.fold_right ~init:[] hs ~f:()
      union @@ List.map hs ~f:(fun (g,h) -> (g, hfind)
  | HCmps (_,_) -> assert false *)
let rec hfind_li (heap: heap) longident : term =
  (* let (>>=) = Option.(>>=) in  *)
  let default = li ~heap longident in
  match heap with
  | HDefined xs -> List.Assoc.find xs ~equal:MyIdent.equal longident
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
*)

let types_hack info1 info2 =
  match info1,info2 with
  | (Some typ1, Some typ2) ->
      (* Format.printf "types_hack '%a' and '%a'\n%!" Printtyp.type_expr typ1 Printtyp.type_expr typ2; *)
      let s1 = Format.asprintf "%a" Printtyp.type_expr typ1 in
      let s2 = Format.asprintf "%a" Printtyp.type_expr typ2 in
      if phys_equal typ1 typ2
        || (String.equal s1 "int" && String.equal s2 "int ref")
        || (String.equal s2 "int" && String.equal s1 "int ref")
      then
        (* let () = Format.printf "It happend\n%!" in  *)
        true
      else false
  | _ -> false


let term_of_heap_loc loc typ =
  match loc with
  | LoIdent id -> ident id typ
  | LoAddr addr_ndx -> link addr_ndx typ

let heap_loc_of_ident id = LoIdent id
let ident_of_heap_loc_exn = function
  | LoAddr _ as loc -> failwiths "Heap location is an address %s on %s %d" (GT.show heap_loc loc) __FILE__ __LINE__
  | LoIdent id -> id

let name_of_heap_loc = function
  | LoIdent id -> Ident.name id
  | LoAddr n -> Printf.sprintf "__loc_%d" n
let pp_heap_loc fmt x = Format.fprintf fmt "%s" (name_of_heap_loc x)


exception TypesShouldBeSame of MyTypes.type_expr * MyTypes.type_expr

(* FAT dot a.k.a. • *)
let rec hdot_defined hs term =
  match term with
  | LI (None, Ident (ident,_), typ) -> read_ident_defined hs ident typ
  | LI (None, key, typ) -> begin
(*      Format.printf "TODO: check that implementation is OK %s %d\n%!" __FILE__ __LINE__;*)
      match hdot_defined hs key with
      | Ident (ident,_) -> read_ident_defined hs ident typ
      | Reference (loc, _) -> read_defined hs (LoAddr loc) typ
      | _ -> failwith "Not implemented"
      end
  | LI (Some hs2, Ident (ident,_), typ) ->
      read_ident_generalized (hcmps (hdefined hs) hs2) ident typ
  | LI (Some hs2, _, typ) ->
      Format.printf "TODO: check that implementation is OK %s %d\n%!" __FILE__ __LINE__;
      term
  | Reference (loc, typ) -> term
  | Ident (_, _) ->
    (* Terms that are concrente adn a priori known should not be affected my heap mutation *)
    term
  | Builtin _ -> term
  (* | BinOp (op, l, r, typ) -> BinOp (op, hdot_defined hs l, hdot_defined hs r, typ) *)
  | Unit
  | CBool _
  | CInt _ -> term
  | Union us     -> union @@ List.map us ~f:(fun (g,t) ->
                      ( simplify_term @@ hdot_defined hs g
                      , hdot_defined hs t)
                    )
  | Call (f, args, typ) ->
      (* Format.eprintf "TODO: not implemented %s %d\n%!" __FILE__ __LINE__; *)
      Call (hdot_defined hs f, List.map args ~f:(hdot_defined hs), typ)
  | Lambda _ ->
      Format.eprintf "TODO: not implemented %s %d\n%!" __FILE__ __LINE__;
      term

and read_defined hs key typ =
  if Defined.has_key hs key
  then
    let (typ2,term) = Defined.find_exn hs ~key in
    (*if not (GT.eq MyTypes.type_expr typ typ2)
      then raise (TypesShouldBeSame (typ, typ2));*)
    (* TODO: equality doesn't work as expected. It seem that structual equality
      is not a right thing here *)
    term
  else
    (* list of pairs (heap_loc*term) that can collide with location [loc] *)
    let may_equal =
      Defined.filter hs ~f:(fun (k,(_,v)) -> types_hack typ.si_typ (type_of_term v))
    in

    let positives = Defined.filter_map may_equal ~f:(fun (k,(typk,v)) ->
      Some (pf_eq (term_of_heap_loc k typk) (term_of_heap_loc key typ), v)
    )
    in
    let neg = pf_conj_list @@ List.map may_equal ~f:(fun (k,_) ->
      pf_not @@ pf_eq (term_of_heap_loc k typ) (term_of_heap_loc key typ) )
    in
    union @@ (neg, li (term_of_heap_loc key typ) typ) :: positives
and read_ident_defined hs (loc: MyIdent.t) typ =
  read_defined hs (LoIdent loc) typ
and write_ident_defined hs loc newval typ =
  let ans = write_ident_defined_helper hs loc newval typ in
  assert (Defined.no_paired_bindings ans);
  ans
and write_ident_defined_helper (hs: defined_heap) loc (newval: term) typ: defined_heap =
  (* Format.printf "write_ident_defined:\n\theap keys = %a\n%!"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ") (fun fmt (i,_) -> GT.fmt MyIdent.t fmt i)) hs;
  Format.printf "\tident is '%a'\n%!" (GT.fmt MyIdent.t) ident;
  Format.printf "\tterm is '%a'\n%!" (GT.fmt Vtypes.term) newval; *)
  let hs = Defined.remove_key hs loc in
  let cond  =
    match type_of_term newval with
    | Some typ -> begin
          fun _ v ->
            types_hack (Some typ) (type_of_term v)
    end
    | None -> (fun _ v -> print_endline "HERR"; true)
  in
  let (may_be_equal,new_hs) =
    Defined.hacky_fold hs ~cond
      ~f:(fun k oldval ->
            union2 (pf_eq  (term_of_heap_loc k typ) (term_of_heap_loc loc typ)) newval
                   (pf_neq (term_of_heap_loc k typ) (term_of_heap_loc loc typ)) oldval)
  in
  if List.is_empty may_be_equal
  then (* it is absolutely new location *)
    (loc, (typ,newval)) :: hs
  else
    let negatives = pf_conj_list @@ List.map may_be_equal
        ~f:(fun k -> pf_not @@ pf_eq (term_of_heap_loc k typ) (term_of_heap_loc loc typ))
   in
    (* FIXME: in case of new location should it really be a union of 1 case ? *)
    let u = union [ (negatives, newval) (*; (pf_not neg, li ident) *) ] in
    (* Checking for empty union is important unless we want shitty shit in the result *)
    if is_empty_union u (* || Defined.has_key hs ident *)
    then new_hs else Defined.add new_hs loc u typ


(**
 *
 *)
and hcmps_defined ms ns : defined_heap =
  fold_defined ns ~init:ms ~f:(fun acc (k,(typ, term)) ->
    let v = simplify_term @@ hdot_defined ms term in
    (* Format.printf "\t\t\t\t v = %a\n%!" (GT.fmt Vtypes.term) v; *)
    write_ident_defined acc k v typ
  )
and hdot_generalized heap term =
  match heap with
  | HDefined hs -> hdot_defined hs term
  | _ -> GT.transform Vtypes.term
    (fun fself -> object
      inherit [_,_] gmap_term_t fself
      method! c_LI () _ h ident typ =
        LI ( Option.some @@ hcmps heap (Option.value h ~default:hempty), ident, typ)
      method! c_Reference () _ loc sinfo =
        li (Reference (loc, sinfo)) ~heap sinfo
    end)
    ()
    term
and read_ident_generalized heap (id: MyIdent.t) typ =
  read_generalized heap (heap_loc_of_ident id) typ
and read_generalized heap (id: heap_loc) typ =
  match heap with
  | HDefined hs -> read_defined hs id typ
  | _ ->
      match id with
      | LoIdent id -> li ~heap (ident id typ) typ
      | LoAddr addr -> li ~heap (link addr typ) typ

and hcmps : heap -> heap -> heap = fun l r ->
  let ans =
    match (l,r) with
    | (HDefined [], h) -> h
    | (h, HDefined []) -> h
    | (HDefined xs, HDefined ys) ->
        let ans  = HDefined (hcmps_defined xs ys) in
        (* Format.printf "\t\t\t\t%a\n%!" (GT.fmt heap) ans; *)
        ans
    | (HDefined xs, HMerge phs) ->
        hmerge_list @@ List.map phs ~f:(fun (g,h) ->
          ( simplify_term @@ hdot_defined xs  g
          , hcmps l h )
        )
    | (HDefined _ as x, HCmps (HDefined _ as y, z)) -> hcmps (hcmps x y) z
    | (_, HCmps(_,_))
    | (HCmps(_,_), _) -> HCmps (l,r)
    | h, HWrite (h2, id, v) -> HWrite (hcmps h h2, id, hdot_generalized h v)
    | HWrite (h, id, v), HMerge xs -> HCmps (l,r)
    | HMerge _, HMerge _
    | _,HCall(_,_)
    | HCall (_,_),_ -> HCmps (l,r)
    | HMerge _, HDefined _ -> HCmps (l,r)
    | HWrite _, HDefined _ -> HCmps (l,r)
  in
(*  Format.printf "calling hcmps of\n%!";
  Format.fprintf Format.std_formatter "\t%s\n%!" (pp_heap () l);
  Format.printf "\t%s\n%!" (pp_heap () r);
  Format.printf "\tresult = %s\n%!" (pp_heap () ans);*)
  ans

let (%%%) = hcmps

let rec hdot h t = hdot_generalized h t
  (*match h,t with
  | HDefined [],_ -> t
  | HDefined hs,_ -> hdot_defined hs t
  | _, Call (Builtin op, args, typ) ->
      call (Builtin op) (List.map args ~f:(hdot h)) typ
  | _, Link (loc,typ_opt) -> li (LoAddr loc) ~heap:h typ_opt
  | _, LI (heap, loc, info) ->
    li ~heap:(h %%% Option.value heap ~default:hempty) loc info
  | _ ->
    Format.printf "hdot: heap = @[%a@]\n%!" (GT.fmt  heap) h;
    Format.printf "      term = @[%a@]\n%!" (GT.fmt  term) t;
    Format.printf "           = @[%s@]\n%!" (GT.show term t);
    failwiths "not implemented %s %d" __FILE__ __LINE__*)

(* let rec heap_subst heap lident new_term =
  Format.eprintf "heap_subst not implemented\n%!";
  heap
and term_subst term lident new_term =
  Format.eprintf "heap_subst not implemented\n%!";
  term *)


let bubble_disj_term troot =
  let rec helper t = t
  in
  helper troot


let report_error = function
  | TypesShouldBeSame (t1, t2) ->
      Location.errorf ~loc:Location.none
       "@[Types mismatch %a@ and %a@]"
       (GT.fmt MyTypes.type_expr) t1
       (GT.fmt MyTypes.type_expr) t2
  | _ -> assert false

let () =
  Location.register_error_of_exn (fun x ->
(*    Format.printf "%s %d\n%!" __FILE__ __LINE__;*)
    match x with
    | TypesShouldBeSame (_,_) as err -> Some (report_error err)
    | _ -> None
  )
