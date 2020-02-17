open Vtypes
open Vpredef

let pp_term () t =
  Format.asprintf "%a" term.GT.plugins#fmt t

let pp_heap () (h: heap) = Format.asprintf "%a" (GT.fmt heap) h

let fold_defined ~f ~init = List.fold_left ~init ~f

let rec type_of_term root =
(*  let wrap desc = { Types.level = 0; scope = None; id=0; desc } in*)
  match root with
  | Union [] -> None
  | Union ((_,t)::_) -> type_of_term t
  | CInt _  -> Some Predef.type_int
  | CBool _ -> Some Predef.type_bool
  | Unit    -> Some Predef.type_unit
  | LI (_,_,t)
  | Ident (_,t)
  (* | BinOp (_,_,_,t) *)
  | Lambda {lam_typ = t}
  | Call (_,_,t) -> Some t
  | Builtin b -> match b with
  | BiPhysEq
  | BiStructEq -> Some Vpredef.type_eq
  | BiMinus
  | BiPlus -> Some Vpredef.type_int_arith
  | BiLT | BiLE | BiGE
  | BiGT -> Some Vpredef.type_int_cmp
  | BiOr
  | BiAnd -> Some Vpredef.logical_and
  | BiNeg -> Some Vpredef.logical_neg

  (* | _ -> failwiths "Not implemented %s %d" __FILE__ __LINE__ *)

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

(** Term operations *)
let call fexpr args typ =
  (* Format.eprintf "constructing call of '%s' to '%s'\n" (pp_term () fexpr)  (pp_term () arg); *)
  match args with
  | [] -> fexpr
  | args ->  simplify_term @@ Call (fexpr, args, typ)

let cint n = CInt n
let cbool b = CBool b
let cunit = Unit
let lambda lam_is_rec lam_argname ~arg_type lam_api lam_eff lam_body lam_typ =
  simplify_term @@ Lambda
    { lam_argname
    ; lam_argtype=arg_type
    ; lam_api; lam_eff; lam_body; lam_is_rec; lam_typ
    }
let li ?heap longident typ = LI (heap, longident, typ)
let ident longident typ = Ident (longident, typ)
let term_biAnd : term = Builtin BiAnd
let conj a b term_typ =
  Call (term_biAnd, [a;b], Predef.type_bool)


let binop op a b typ = simplify_term @@ Call (op, [a;b], typ)
let unop  op arg typ = simplify_term @@ Call (op, [arg], typ)

let union xs =
  (* Printexc.print_raw_backtrace stdout (Printexc.get_callstack 2); *)
  (* TODO: optimize Union [ ⦗("n_1635" < 0), x⦘; ⦗¬("n_1635" < 0), x⦘] *)
  (*match simplify_guards xs with*)
  match xs with
  (* | [] -> failwiths "FIXME: Introduce unreachable term for empty union." *)
  | [(CBool true, t)] -> t
  (*| [ (g1,x); (g2,y)] when (GT.eq Vtypes.term x y)
        && (GT.eq Vtypes.term g1 (Not g2) || GT.eq Vtypes.term g2 (Not g1)  )
      -> x*)
  | xs ->
      let reduced =
        List.concat_map xs ~f:(fun (g,t) ->
          match t with
          | Union inners -> List.map inners ~f:(fun (k,v) ->
              let new_g = call (Builtin BiAnd) [g; k] Predef.type_bool in
              (simplify_term new_g, v)
            )
          | _ -> [ (g,t) ]
          )
      in
      Union reduced
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
let builtin op = Builtin op
let pf_binop op f1 f2 typ = call (Builtin op) [f1; f2] typ
let pf_conj l r = pf_binop BiAnd l r Vpredef.type_bool
let pf_not t =
  call (Builtin BiNeg) [ t ] Vpredef.type_bool
let pf_neq t1 t2 =
  pf_not @@ call (Builtin BiStructEq) [ t1; t2 ] Vpredef.type_bool
let pf_eq t1 t2 =
  (* if (String.equal (MyIdent.to_string id1) "loop_1637" &&
      String.equal (MyIdent.to_string id2) "ndx_1003"
    )
  then assert false; *)

  (* TODO: simplify arguments *)
  call (Builtin BiStructEq) [ t1; t2 ] Vpredef.type_bool
  (*simplify_pf @@ EQident (id1, id2)*)

let pf_conj_list = function
  | [] -> CBool true
  | h::hs -> List.fold_left ~init:h hs ~f:pf_conj

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

let types_hack : Types.type_expr -> Types.type_expr -> bool = fun typ1 typ2 ->
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

exception TypesShouldBeSame of MyTypes.type_expr * MyTypes.type_expr

(* FAT dot a.k.a. • *)
let rec hdot_defined hs term =
  match term with
  | LI (None, ident, typ) -> read_ident_defined hs ident typ
  | LI (Some hs2, ident, typ) ->
      read_generalized (hcmps (hdefined hs) hs2) ident typ
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

and read_ident_defined hs loc typ =
  if List.Assoc.mem hs loc ~equal:MyIdent.equal
  then
    let (typ2,term) = List.Assoc.find_exn hs loc ~equal:MyIdent.equal in
    (*if not (GT.eq MyTypes.type_expr typ typ2)
      then raise (TypesShouldBeSame (typ, typ2));*)
    (* TODO: equality doesn't work as expected. It seem that structual equality
      is not a right thing here *)
    term
  else
    let may_equal =
      Defined.filter hs ~f:(fun (k,(_,v)) ->
        match Option.map (type_of_term v) ~f:(types_hack typ) with
        | None -> (* union or something *) true
        | Some b -> b
      )
    in

    (* We should return UNION here *)
    let positives = List.filter_map may_equal ~f:(fun (k,(typk,v)) ->
      Some (pf_eq (ident k typk) (ident loc typ), v)
    )
    in
    let neg = pf_conj_list @@ List.map may_equal ~f:(fun (k,_) ->
      pf_not @@ pf_eq (ident k typ) (ident loc typ) )
    in
    union @@ (neg, li loc typ) :: positives


and write_ident_defined (hs: defined_heap) loc (newval: term) typ: defined_heap =
  (* Format.printf "write_ident_defined:\n\theap keys = %a\n%!"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ") (fun fmt (i,_) -> GT.fmt MyIdent.t fmt i)) hs;
  Format.printf "\tident is '%a'\n%!" (GT.fmt MyIdent.t) ident;
  Format.printf "\tterm is '%a'\n%!" (GT.fmt Vtypes.term) newval; *)
  let cond  =
    match type_of_term newval with
    | Some typ -> begin
          fun _ v ->
            match Option.map (type_of_term v) ~f:(types_hack typ) with
            | None -> (* union or something *) true
            | Some b -> b
    end
    | None -> (fun _ v -> print_endline "HERR"; true)
  in
  let (may_be_equal,new_hs) =
    Defined.hacky_fold hs ~cond
      ~f:(fun k oldval ->
            union2 (pf_eq  (ident k typ) (ident loc typ)) newval
                   (pf_neq (ident k typ) (ident loc typ)) oldval)
  in
  if List.is_empty may_be_equal
  then (* it is absolutely new location *)
    (loc, (typ,newval)) :: hs
  else
    let negatives = pf_conj_list @@ List.map may_be_equal
        ~f:(fun k -> pf_not @@ pf_eq (ident k typ) (ident loc typ))
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
    end)
    ()
    term
and read_generalized heap ident typ =
  match heap with
  | HDefined hs -> read_ident_defined hs ident typ
  | _ -> li ~heap ident typ

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
  Format.printf "calling hcmps of\n%!";
  Format.fprintf Format.std_formatter "\t%s\n%!" (pp_heap () l);
  Format.printf "\t%s\n%!" (pp_heap () r);
  Format.printf "\tresult = %s\n%!" (pp_heap () ans);
  ans

let hdot heap term =
  match heap with
  | HDefined [] -> term
  | HDefined hs -> hdot_defined hs term
  | _ -> failwiths "not implemented %s %d" __FILE__ __LINE__

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

module Api = struct
  type t = api * MyIdent.t list
  let empty: t = (MyAPI MyIdent.Map.empty, [])

  (* let fold_api ~f ~init xs = List.fold_left ~f ~init xs *)
  let add ((MyAPI api,pen):t) k v =
    (MyAPI (MyIdent.Map.add k v api), pen)

  let add_pending (api,xs) new_ = (api,new_::xs)

  let remove_pending_exn (api,xs) el = (api, List.filter xs ~f:(MyIdent.equal el))

  let is_pending (_,xs) ident : bool = Base.List.exists xs ~f:(MyIdent.equal ident)
  (* let is_pending_lident (_,xs) (lident: Longident.t) : MyIdent.t option =
    assert false *)

  let is_recursive_exn (MyAPI api,pend) ident =
    List.mem pend ident ~equal:MyIdent.equal ||
    match MyIdent.Map.find ident api  with
    | (Recursive,_) -> true
    | (Nonrecursive,_) -> false

  let find_ident_exn : t -> Ident.t -> rec_flag * term = fun (MyAPI api,_toplevel) ident ->
    MyIdent.Map.find ident api

    (* List.find_map_exn api ~f:(fun (k,flg,t) ->
      if MyIdent.equal ident k
      then Some (flg,t)
      else None
    ) *)
    (* List.find_exn api ~f:(fun (k,flg,t) -> )
    List.Assoc.find_exn ~equal:MyIdent.equal api ident *)
  let find_ident_li : t -> Ident.t -> MyTypes.type_expr -> term = fun (api,toplevel) ident typ ->
    try snd @@ find_ident_exn (api,toplevel) ident
    with Not_found -> li ident typ


end

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
