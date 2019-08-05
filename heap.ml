open Vtypes

let pp_term () t =
  Format.asprintf "%a" term.GT.plugins#fmt t

let pp_heap () h = Format.asprintf "%a" heap.GT.plugins#fmt h

let fold_defined ~f ~init = List.fold_left ~init ~f

(** Simplification *)
let eval_binop = function
  | Plus  -> (fun x y -> CInt  (x+y))
  | Minus -> (fun x y -> CInt  (x+y))
  | LT    -> (fun x y -> CBool (x<y))
  | LE    -> (fun x y -> CBool (x<=y))
  | GT    -> (fun x y -> CBool (x>y))
  | GE    -> (fun x y -> CBool (x>=y))
  | Eq    -> (fun x y -> CBool (x=y))

let rec simplify_term = function
  | BinOp (op,l,r) -> begin
      match (simplify_term l, simplify_term r) with
      | (CInt n, CInt m) -> eval_binop op n m
      | (l,r) -> BinOp (op,l,r)
  end
  | term -> term

let rec simplify_pf = function
  | Not ph -> begin
      match simplify_pf ph with
      | EQident (l,r) when Ident.equal l r -> PFFalse
      | Not ph  -> ph
      | PFTrue  -> PFFalse
      | PFFalse -> PFTrue
      | ph      -> Not ph
    end
  | EQident (l,r) when Ident.equal l r -> PFTrue
  | ph -> ph

let simplify_guards gs =
  let exception QQQ in
  List.filter_map gs ~f:(fun (ph, term) ->
    match simplify_pf ph with
    | PFTrue -> Some (PFTrue, simplify_term term)
    | PFFalse -> None
    | pf -> Some (pf, simplify_term term)
  )

(** Term operations *)
let call fexpr arg =
  (* Format.eprintf "constructing call of '%s' to '%s'\n" (pp_term () fexpr)  (pp_term () arg); *)
  simplify_term @@ Call (fexpr, arg)
let cint x = CInt x
let cbool b = CBool b
let cunit = Unit
let lambda lam_is_rec lam_argname lam_api lam_eff lam_body =
  simplify_term @@ Lambda { lam_argname; lam_api; lam_eff; lam_body; lam_is_rec }
let li ?heap longident = LI (heap, longident)
let union xs =
  match simplify_guards xs with
  (* | [] -> failwiths "FIXME: Introduce unreachable term for empty union." *)
  | [(PFTrue, t)] -> t
  | xs -> Union xs
let union2 g1 t1 g2 t2 = union [(g1,t1); (g2,t2)]
let binop op a b = simplify_term @@ BinOp (op,a,b)

let is_empty_union = function
  | Union [] -> true
  | _ -> false

(** Propositonal formula operations *)

let pf_term el = Term el
let pf_not pf = simplify_pf @@ Not pf
let pf_binop op f1 f2 = simplify_pf @@ LogicBinOp (op, f1, f2)
let pf_eq id1 id2 = simplify_pf @@ EQident (id1, id2)
let pf_neq id1 id2 = simplify_pf @@ pf_not @@ EQident (id1, id2)
let pf_conj_list = function
  | [] -> PFTrue
  | h::hs -> List.fold_left ~init:h hs ~f:(pf_binop Conj)

(** Heap construction *)
let hempty : t = HEmpty
let hdefined xs = HDefined xs
let hsingle name el : t = hdefined [(name,el)]
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

(* FAT dot a.k.a. • *)
let rec hdot_defined hs term =
  match term with
  | LI (None, ident) -> read_ident_defined hs ident
  | LI (Some hs2, ident) -> 
      read_generalized (hcmps (hdefined hs) hs2) ident
  | BinOp (op, l, r) -> BinOp (op, hdot_defined hs l, hdot_defined hs r)
  | Unit
  | CBool _
  | CInt _ -> term
  | Union us     -> union @@ List.map us ~f:(fun (g,t) ->
                      ( simplify_pf @@ GT.gmap pf (hdot_defined hs) g
                      , hdot_defined hs t)
                    )
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

and write_ident_defined hs ident (newval: term) : defined_heap =
  let neg = pf_conj_list @@ List.map hs ~f:(fun (k,_) -> pf_not @@ pf_eq k ident) in
  let hs = List.map hs ~f:(fun (k,oldval) ->
      (k, union2 (pf_eq k ident) newval (pf_neq k ident) oldval)
  )
  in
  (* FIXME: in case of new location should it really be a union of 1 case ? *)
  let u = union [ (neg, newval) (*; (pf_not neg, li ident) *) ] in
  (* Checking for empty union is important unless we want shitty shit in the result *)
  if is_empty_union u then hs else (ident,u) :: hs

(**
 *
 *)
and hcmps_defined ms ns : defined_heap =
  fold_defined ns ~init:ms ~f:(fun acc (k,v) ->
    let v = simplify_term @@ hdot_defined ms v in
    write_ident_defined acc k v
  )
and hdot_generalized heap term = 
  term
and read_generalized heap ident = li ~heap ident
and hcmps : t -> t -> t = fun l r ->
  (* Format.eprintf "calling hcmps of\n%!";
  Format.eprintf "\t%s\n%!" (pp_heap () a);
  Format.eprintf "\t%s\n%!" (pp_heap () b); *)
  match (l,r) with
  | (HEmpty, h) -> h
  | (h, HEmpty) -> h
  | (HDefined xs, HDefined ys) -> HDefined (hcmps_defined xs ys)
  | (HDefined xs, HMerge phs) -> 
      hmerge_list @@ List.map phs ~f:(fun (pf,h) -> 
        ( simplify_pf @@ (GT.gmap Vtypes.pf) (hdot_defined xs) pf
        , hcmps l h )
      )
  | (_, HCmps(_,_))
  | (HCmps(_,_), _) -> HCmps (l,r)
  | h, HWrite (h2, id, v) -> HWrite (hcmps h h2, id, hdot_generalized h v)
  | HWrite (h, id, v), HMerge xs -> HCmps (l,r)
  | HMerge _, HMerge _
  | _,HCall(_,_) 
  | HCall (_,_),_ -> HCmps (l,r)
  | HMerge _, HDefined _ -> HCmps (l,r)
  | HWrite _, HDefined _ -> HCmps (l,r)
  

let hdot heap term =
  match heap with
  | HDefined hs -> hdot_defined hs term
  | HEmpty      -> term
  | _ -> failwiths "not implemented %s %d" __FILE__ __LINE__

(* let rec heap_subst heap lident new_term =
  Format.eprintf "heap_subst not implemented\n%!";
  heap
and term_subst term lident new_term =
  Format.eprintf "heap_subst not implemented\n%!";
  term *)

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
