open Base
open Printf
open Typedtree
open Vtypes
open Vutils

module UntypeP = struct
  let expr e =
    let untyped = Untypeast.default_mapper.expr Untypeast.default_mapper e in
    Format.asprintf "%a" (Printast.expression 0) untyped;
end

let (%%%) = Heap.(%%%)

(* let is_arr expr =
  match expr.exp_type.Types.desc with
  | Tarrow (_,_,_,_) -> true
  | _ -> false *)

(* let i_to_longi i = Longident.Lident (Ident.unique_name i) *)

(* let standart_heap = Heap.hempty *)
  (* Heap.single (Lident "!") (Heap.lambda (Some (Lident "x")) Heap.empty (Heap.li (Heap.empty) (Lident "x"))) *)

let is_binop = function
  | "<=" | "<" | ">" | ">=" | "+" | "-" | "||" -> true
  | _ -> false

let classify_binop = function
  | "<=" -> Some (Vtypes.BiLE, Predef.type_bool)
  | "<"  -> Some (Vtypes.BiLT, Predef.type_bool)
  | ">"  -> Some (Vtypes.BiGT, Predef.type_bool)
  | ">=" -> Some (Vtypes.BiGE, Predef.type_bool)
  | "+"  -> Some (Vtypes.BiPlus,  Predef.type_int)
  | "-"  -> Some (Vtypes.BiMinus, Predef.type_int)
  | "||" -> Some (Vtypes.BiOr,    Predef.type_bool)
  | "&&" -> Some (Vtypes.BiAnd,   Predef.type_bool)
  | "="  -> None
  | _    -> None

exception IdentNotFound of heap_loc  * string
let ident_not_found loc fmt =
  Format.ksprintf (fun s -> raise (IdentNotFound (loc, s))) fmt

let find_heap_loc api heap loc typ =
  match Heap.Api.is_pending api loc with
  | true ->
      let sinfo = make_sinfo ~typ () in
      Heap.li ~heap (Heap.term_of_heap_loc loc sinfo) sinfo
  | false ->
      match Heap.Api.find_exn api loc with
      | (_,term,_) -> term
      | exception Not_found
      | exception Not_found_s _ ->
          ident_not_found loc "find_lident: can't find on ident '%s'" (Heap.name_of_heap_loc loc)

let find_ident api heap ident typ =
  find_heap_loc api heap (Heap.heap_loc_of_ident ident) typ


let apply_old_api api term =
  (* *)
  term


let rec process_str api { str_items; _ } : Heap.Api.t * Vtypes.t =
  List.fold_left ~init:(api, Heap.hempty) str_items
    ~f:(fun acc si ->
          match process_si acc si with
          | None -> acc
          | Some rez -> rez
       )
and process_si (api,heap) { str_desc; _} : (Heap.Api.t * Vtypes.t) option =
  match str_desc with
  | Tstr_attribute _ -> None
  | Tstr_value (recflg, [vb]) -> begin
    match process_vb (api, Heap.hempty) recflg vb with
    | (api, Some ident, ans, heff) ->
        Some  ( Heap.Api.add api (Heap.heap_loc_of_ident ident) (recflg, ans, heff)
              , Heap.hcmps heap heff)
    | _ -> assert false
  end
  | Tstr_value (recflg, vbs) -> assert false
  | _ -> assert false
and process_vb (api,heap) recflg { vb_pat; vb_expr; _ } : Heap.Api.t * MyIdent.t option * Vtypes.term * Vtypes.t =
  (* returns maybe identifier,
   * rhs effect,
   * effect thats is created by binding creation *)
  (* Format.eprintf "process_vb: ... = '%s'\n%!" (UntypeP.expr vb_expr); *)
  match vb_pat.pat_desc with

  | Tpat_var (ident,_) ->
      let api = match recflg with
        | Nonrecursive -> api
        | Recursive ->
            (* let api = Heap.Api.add api ident (Heap.li ident) in *)
            Heap.Api.add_pending_ident api ident
      in
      let (api,eff,ans) = process_expr (api, Heap.hempty) vb_expr in
      FCPM.is_caml_ref vb_expr
        ~ok:(fun _ ->
              ( Heap.Api.mark_unique api (Heap.heap_loc_of_ident ident)
              , Some ident
              , ans
              , heap %%% eff %%% (Heap.hsingle (Heap.heap_loc_of_ident ident) ans (make_sinfo ~typ:vb_expr.exp_type ()) ))
          )
        (fun () -> (api, Some ident, ans, heap %%% eff) )
      (* (api, Some ident, ans, heap %%% eff) *)
  | _ ->
      failwiths "TODO: %s %d" __FILE__ __LINE__


(** Accepts
 * 1) Current state of API
 * 2) current accumulated effect
 * 3) expression to process
 * Returns
 * 1) new API
 * 2) accumulated effect combined with previous one
 * 3) term result
 *)
and process_expr (api,heap) e =
  match e.exp_desc with
  | Texp_constant (Asttypes.Const_int n) -> (api, Heap.hempty, Heap.cint n)
  | Texp_construct ({txt=Lident "()"},_,[]) -> (api, Heap.hempty, Heap.cunit)
  | Texp_ident (Pident ident, _, { val_type }) ->
    (* TODO: use path here *)
    (* TODO: Where should I unroll functions? *)
    (* identifiers are returned as is. No inlining yet, even for functions *)
    Format.printf "HERR: %a\n%!" (GT.fmt MyIdent.t) ident;
    let t =
      match find_ident api heap ident val_type with
(*      | Link (_,_) as lnk -> lnk*)
      | exception IdentNotFound (_,_)
      | Vtypes.Lambda  _
      | _ ->
        let sinfo = make_sinfo ~typ:val_type () in
        Heap.li_ident ident sinfo
    in
    (api, heap, t)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_construct({txt=Lident "()"},_,[])}; c_rhs}] } ->
        (* Processing `fun () -> c_rhs` *)
    let api, h, ans = process_expr (api,heap) c_rhs in
    (* Format.eprintf "%s %d %a\n%!" __FILE__ __LINE__ Vtypes.t.GT.plugins#fmt h; *)
    let arg_type = make_sinfo ~typ:Vpredef.type_unit () in
    (api, Heap.hempty, Heap.lambda false None ~arg_type Heap.Api.(api.api) h ans (make_sinfo ~typ:e.exp_type ()))

  | Texp_function { param; cases=[{c_guard=None; c_lhs={pat_desc=Tpat_var(argname,_)}; c_rhs}] } ->
        (* Processing `fun argname -> c_rhs` *)
      (* let api = Heap.Api.add api param (Heap.li param) in *)
      let api, h, ans = process_expr (api,heap) c_rhs in

      (* Format.eprintf "%s %d %a\n%!" __FILE__ __LINE__ Vtypes.t.GT.plugins#fmt h; *)
      let arg_type = match e.exp_type.Types.desc with
      | Tarrow (_,arg,_,_) -> make_sinfo ~typ:arg ()
      | _ -> failwith "Can get type of function's argument. should not happen"
      in
      (api, Heap.hempty, Heap.lambda false (Some argname) ~arg_type Heap.Api.(api.api) h ans (make_sinfo ~typ:e.exp_type ()))

  | Texp_let (recflg, [vb], body) -> begin
      match process_vb (api,heap) recflg vb with
      | (api, Some ident, rhs, heff) ->
          (* we don't care about isolation here, so we compose heaps with toplevel one *)
          let api = Heap.Api.add api (Heap.heap_loc_of_ident ident) (recflg,rhs, heff) in
          let heap = heap %%% heff in
          let heap = heap %%% (Heap.hsingle (Heap.heap_loc_of_ident ident) rhs (make_sinfo ~typ:vb.vb_expr.exp_type ())) in
          (* we need to extend API before processing the body *)
          let api, heff3, ans = process_expr (api,heap) body in
          (api, heff3, ans)
      | _ -> assert false
  end
  | Texp_let (_recflg, _vbs, _body) -> assert false

  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "ref"},_)}, [(_,Some e)])
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Ldot(Lident _, "ref")},_)}, [(_,Some e)]) ->
      let api, h, t1 = process_expr (api, heap) e in
      let (link_id, link) = Heap.new_link (make_sinfo ~typ:e.exp_type ()) in
      let eff = Heap.hsingle (LoAddr link_id) t1 (make_sinfo ~typ:e.exp_type ()) in
      (api, h %%% eff, link)
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident opname},{val_type})}, [(_,Some l); (_,Some r) ])
        when Option.is_some (classify_binop opname) -> begin
    (* binop *)
    let op,_ = Base.Option.value_exn  (classify_binop opname) in
    (* Although we don't need to return updated API we return it
     * to have a global cache of function summaries *)

    let api_1,h1,l2 = process_expr (api,heap) l in
    let api_2,h2,r2 = process_expr (api_1,h1) r in
    (api_2, h2, Heap.binop (Heap.builtin op) l2 r2 (make_sinfo ~typ:e.exp_type ()))
  end
  | Texp_apply ({exp_desc=Texp_ident(Pdot (Pident _ident,":="), _, _)},
               [(_,Some {exp_desc=Texp_ident(Pident ident,_,_)}); (_,Some rhs) ]) -> begin
        (* ident := rhs *)
    (* Format.eprintf "Tracing '%s'" (UntypeP.expr e); *)
    let api_1,h1,r1 = process_expr (api,heap) rhs in
    (* Format.eprintf "%s %d %a\n" __FILE__ __LINE__ Vtypes.t.GT.plugins#fmt h1; *)
    let heap_ans = h1 %%% Heap.hsingle (Heap.heap_loc_of_ident ident) r1 (make_sinfo ~typ:rhs.exp_type ()) in
    (api_1, heap_ans, Heap.cunit)
    (* match Heap.Api.find_ident_exn api ident with
    | Heap.LI (h,ident) ->
      let heap_ans = Heap.hcmps h1 (Heap.hsingle ident r1) in
      (* The idea is to have all optimisation operations in Heap module *)
      (api_1, heap_ans, Heap.Unit)
    | z -> failwith @@ Format.sprintf "not implemented. Expected LI but got '%a'" Heap.pp_term z *)
  end
  | Texp_apply ({exp_desc=Texp_ident(Pdot (Pident _ident, "!"), _, _)}, [ (_,Some r) ]) -> begin
    let api,h,r = process_expr (api,heap) r in
    (api,h, Heap.li r (make_sinfo ~typ:e.exp_type ()))
  end
  | Texp_apply ({exp_desc=Texp_ident(Pdot (Pident _ident, "not"), _, {val_type})}, [ (_,Some rhs) ]) ->
    let api,h,r = process_expr (api,heap) rhs in
    (api, h, Heap.unop (Heap.builtin Vtypes.BiNeg) r Heap.sinfo_bool)

  | Texp_apply ({exp_desc=Texp_ident(Pident fident,_,{val_type=ftyp})}, [(Asttypes.Nolabel,Some arg)]) -> begin
    (* Now: real function application *)
    let api,arg_eff,arg_evaled = process_expr (api, Heap.hempty) arg in
    (* now we need to compose effect of e with effect of call
       But for recursive calls -- we shouldn't
     *)
    match find_heap_loc api heap (Heap.heap_loc_of_ident fident) ftyp with
    | exception IdentNotFound (_,_) -> begin
        (* It could be a recursive call *)
        if Heap.Api.is_pending_ident api fident
        then (api, heap, Heap.li_ident fident (make_sinfo ~typ:ftyp ()))
        else failwiths "(should not happen) not implemented %s %d" __FILE__ __LINE__
    end

    | Vtypes.Lambda  _ when Heap.Api.is_pending_ident api fident || Heap.Api.is_recursive_ident_exn api fident ->
        (* recursive functions we left as is *)
        let val_info = make_sinfo ~typ:ftyp () in
        ( api
        , Heap.(hcmps arg_eff (hcall (li_ident fident val_info) [arg_evaled]))
        , Heap.(call (li_ident ~heap fident val_info) [arg_evaled] val_info))
    | Vtypes.Lambda {lam_argname; lam_argtype; lam_eff; lam_api; lam_body} ->
        (* for nonrecursive lambdas we need to compose its effect after binding the argument *)
        let argb = match lam_argname with
          | None -> Heap.hempty
          | Some argname -> Heap.hsingle (Heap.heap_loc_of_ident argname) arg_evaled lam_argtype
        in
        let env_h   = (heap %%% arg_eff) %%% argb in
        let app_eff = env_h %%% lam_eff in
        let app_rez = Heap.hdot env_h lam_body in
        (api, app_eff, app_rez)
        (* (api, Heap.hcmps argeff (Heap.hcall (Heap.li ident) ans), Heap.call (Heap.li ~heap ident) ans) *)
        (* let app_eff = Heap.heap_subst argeff lam_argname ans in
        (api, app_eff, Heap.call (Heap.li ~heap ident) ans) *)
    | Vtypes.LI (h, ident, typ) as func ->
        ( api
        , arg_eff %%% Heap.hcall (Heap.li ident typ) [arg_evaled]
        , Heap.call func [arg_evaled] (make_sinfo ~typ:e.exp_type ()) )
    (* | exception Not_found -> failwith (Printf.sprintf "Identifier unbound: '%a'" Vtypes.MyIdent.pp_string ident) *)
    | ans_term ->
        failwith (sprintf "typecheck error? should not happed. Searched for ident %a. Got '%a'"
                    Vtypes.MyIdent.pp_string fident
                    Heap.pp_term ans_term
                )
  end
  | Texp_apply ({exp_desc=Texp_ident(Pident fident,_,{val_type})}, args) -> begin
      let args = List.map args ~f:(function
        | (Asttypes.Nolabel, Some arg) -> arg
        | _ -> failwiths "labeled arguments not supported (%s %d)\n%!" __FILE__ __LINE__
      )
      in
      (* Format.printf "Got multiple (%d) arguments\n%!" (List.length args); *)
      match find_ident api heap fident val_type with
      | exception IdentNotFound (_,_) -> begin
        (* It could be a recursive call *)
        if Heap.Api.is_pending_ident api fident
        then (api, heap, Heap.li_ident fident (make_sinfo ~typ:val_type ()))
        else failwiths "(should not happen) not implemented %s %d" __FILE__ __LINE__
      end
      | Vtypes.Lambda { lam_eff; lam_body; lam_argname }
                      when Heap.Api.is_pending_ident api fident || Heap.Api.is_recursive_ident_exn api fident ->
        (* for recursive calls we do nothing interesting *)
        (* we evaluate from right to left (native code) and left call in the result *)
        let api, eff, evaled_args =
          List.fold_right args ~init:(api,heap,[])
            ~f:(fun arg (api,acch,rezs) ->
                  let api,arg_eff,arg_evaled = process_expr (api, Heap.hempty) arg in
                  (api, acch %%% arg_eff, arg_evaled :: rezs)
            )
        in
        let finfo = make_sinfo ~typ:val_type () in
        let arginfo = make_sinfo ~typ:e.exp_type () in
        let open Heap  in
        ( api
        , eff %%% Heap.hcall (li_ident fident finfo) evaled_args
        , Heap.call (Heap.ident fident finfo) evaled_args arginfo)
      | Vtypes.Lambda { lam_eff; lam_body; lam_argname } ->
          Format.printf "%s %d\n%!" __FILE__ __LINE__;
          let api, all_args_eff, evaled_args =
            List.fold_right args ~init:(api,heap,[])
              ~f:(fun arg (api,acch,rezs) ->
                    let api,arg_eff,arg_evaled = process_expr (api, Heap.hempty) arg in
                    (api, acch %%% arg_eff, arg_evaled :: rezs)
              )
          in

          (* TODO: rewrite this by evaluating all arguments *)
          let fuck = List.foldk evaled_args
            ~init:(api, Heap.hempty, Heap.hempty, Heap.li_ident ~heap fident (make_sinfo ~typ:val_type ()), lam_eff, lam_body, val_type)
            ~finish:(fun acc -> (acc,[]))
            ~f:(fun ((api, eff, arg_bindings, func, lam_eff, lam_body, typ) as theacc) hterm tl k ->
                  (* We accumulate on the go  1) an effect 2) term 3) the non-applied arguments *)
                  match lam_body with
                  | Vtypes.Lambda { lam_eff=next_eff; lam_body=next_body; lam_argname=(Some nextargname); lam_typ } ->
                    let xxx1 = Heap.hsingle (Heap.heap_loc_of_ident nextargname) hterm lam_typ in
                    let next_bindings = arg_bindings %%% xxx1 in
                    (* acumulated evaluation effect is previous effect + substitution of arguments
                       + eff of applying next argument *)
                    let accum_eff = eff %%% (xxx1 %%% next_eff) in
                    let next_term = Heap.hdot next_bindings next_body in
                    let next_typ =
                      let rec helper t =
                        match t.Types.desc with
                        | Tarrow (_,l,r,_) -> r
                        | Tlink next -> helper next (* unification indirection *)
                        | _ ->
                          failwiths "%s %d unwinding type abbreviations is not implemented: `%s`" __FILE__ __LINE__
                            (Format.asprintf "%a" Printtyp.type_expr typ)
                      in
                      helper typ
                    in
                    k (api, accum_eff, next_bindings, next_term, next_eff,next_body, next_typ)
                  | Vtypes.Lambda { lam_argname= None; _} ->
                      failwiths "not implemented on %s %d" __FILE__ __LINE__
                  | _ ->
                      (* if next is not a lambda, then we should stop (or not?) *)
                      (theacc,tl)
                )
          in
          (match fuck with
          | ((api,acced_eff,_,term_rez,_,_, typ), xs) ->
              (* recursive functions we left as is *)
              ( api
              , heap %%% all_args_eff %%% acced_eff
              , Heap.call term_rez xs (make_sinfo ~typ ()))
          )
      | Vtypes.LI (h, ident, typ) as func ->
          let api, arg_eff, evaled_args =
              List.fold_right args ~init:(api,heap,[])
                ~f:(fun arg (api,acch,rezs) ->
                      let api,arg_eff,arg_evaled = process_expr (api, Heap.hempty) arg in
                      (api, acch %%% arg_eff, arg_evaled :: rezs)
                )
            in
        ( api
        , arg_eff %%% (Heap.hcall (Heap.li ident typ) evaled_args)
        , Heap.call func evaled_args (make_sinfo ~typ:e.exp_type ()))
      | _ -> assert false

  end
  | Texp_sequence (a,b) ->
    let api,effa,___ = process_expr (api,Heap.hempty) a in
    let api,effb,ans = process_expr (api,Heap.hempty) b in
    (api, heap %%% effa %%% effb, Heap.hdot_generalized effa ans)
  | Texp_ifthenelse (econd, ethen, Some eelse) ->
    let (api,h1, e) = process_expr (api,heap) econd in
    let h_after_cond = h1 in
    let (api,h2,th) = process_expr (api,h_after_cond) ethen in
    let (api,h3,el) = process_expr (api,h_after_cond) eelse in
    let notg = Heap.pf_not e in
    (api, Heap.hmerge2     e h2 notg h3, Heap.union2 e th notg el)
  | Texp_match (what, cases, _) -> begin
    Format.printf "HERR\n%!";

    match cases with
    | [{c_lhs={pat_desc=Tpat_construct ({txt=Lident "()"},_,[])}; c_rhs}] ->
        let api, eff, _scrut = process_expr (api,Heap.hempty) what in
        (* Format.printf "eff = %a\n%!" (GT.fmt Vtypes.heap) eff; *)
        let api, nexteff, ans = process_expr (api,Heap.hempty) c_rhs in
        (api, heap %%% eff %%% nexteff, ans)
    | _ -> assert false
  end
  | _ -> failwith ("not implemented " ^ UntypeP.expr e)

(** Extracting properties from OCaml code
  [@@@ prop.propname (fun x y ... -> P)]

  Returns [ warnings * structure_item * (propname option) ]
  *)
let get_properies root =
  let rgxp = Str.regexp "prop\\(\\.\\([a-zA-Z0-9]+\\)\\)?" in
  let ans = ref [] in

  let iterator =
    { Tast_iterator.default_iterator with
      structure_item = (fun self si ->
        match si.str_desc with
        | Tstr_attribute { attr_name={txt; loc}; attr_payload = PStr [e] }
            when Str.string_match rgxp txt 0 ->
              let name = match Str.matched_group 2 txt with
                | s -> Some s
                | exception Not_found -> None
              in
              Ref.replace ans (List.cons (loc, e, name))
        | _ -> ()
      )
    }
  in
  iterator.structure iterator root;
  List.rev !ans

(*
let hornize api exprs =
  let open Format in
  let module VHC = VHornClauses.V2 in
  let rec skip_lambdas t =
    match t with
    | Vtypes.Lambda { lam_body } -> skip_lambdas lam_body
    | t -> t
  in
  let rec helper term : VHC.formula =
    (* Type of term should be bool *)
    match term with
    | CBool b ->
        failwith "Don't know what to do with boolean terms"
(*        VHC.T.bool b*)
    | Call (Builtin BiLE, [Ident (l,_); CInt r], _)
    | Call (Builtin BiGE, [CInt       r; Ident (l,_)], _) ->
        let name = MyIdent.to_string l in
        VHC.(F.le (T.var name) (T.int r))

    | Call (Builtin BiLE, [LI (_,l,_); CInt r], _)
    | Call (Builtin BiGE, [CInt     r; LI (_,l,_)], _) ->
        let name = MyIdent.to_string l in
        VHC.(F.le (T.var name) (T.int r))

    | Call (Builtin BiGT, [a; b], _)
    | Call (Builtin BiLT, [b; a], _) ->
        VHC.(F.gt (helper_term a) (helper_term b))

    | Call (Builtin BiStructEq, [LI (_,l,_); CInt r], _)
    | Call (Builtin BiStructEq, [CInt     r; LI (_,l,_)], _) ->
        let name = MyIdent.to_string l in
        VHC.(F.eq (T.var name) (T.int r))

    | Call (Builtin BiNeg, [ff], _) ->
        VHC.F.neg (helper ff)
    (* | Call (Builtin (BiEq, _), [l;r], _) -> assert false *)

    | Call (LI (_,id,_), args, _) ->
        assert false

    | Call (Builtin BiStructEq, [l; r], _) ->
        (* TODO: bubbling up of result from calls of orelational symbols *)
        VHC.F.eq (helper_term l) (helper_term r)


    (* (f arg arg2 = N) *)
    | Call (Builtin BiStructEq, [Call (LI (_,id,_), args, _); CInt r as rhs ], _) ->
        let name = MyIdent.to_string id in
        VHC.(F.eq
              (T.call_uf name @@
                List.map ~f:helper_term (args @ [rhs]) )
              (helper_term rhs)
            )

    | _ ->
        fprintf std_formatter "%a\n%!" (GT.fmt Vtypes.term) term;
        failwiths "TODO: %s %d" __FILE__ __LINE__

  and helper_term term : VHC.term = match term with
    | CInt n           -> VHC.T.int n
    | Ident (id, _)    -> VHC.T.var (MyIdent.to_string id)
    | LI (None, id, _) -> VHC.T.var (MyIdent.to_string id)
    | Call (Builtin BiMinus, [l; r], _) ->
        VHC.(T.minus (helper_term l) (helper_term r))
    | Call (Builtin BiPlus, [l; r], _) ->
        VHC.(T.plus  (helper_term l) (helper_term r))
    | Call (LI (_,id,_), args, _) ->
        VHC.T.call_uf (MyIdent.to_string id) (List.map args ~f:helper_term)
    | _ ->
        fprintf std_formatter "%a\n%!" (GT.fmt Vtypes.term) term;
        failwiths "TODO: %s %d" __FILE__ __LINE__

  in
  let clauses =
    let rec hack_clause term : VHC.formula list =
      match term with
      | Vtypes.Call (Builtin BiAnd, args, _)  ->
          List.map args ~f:helper
          (* helper n (term,name) Format.std_formatter *)
      | _ -> failwiths "TODO: %s %d" __FILE__ __LINE__
    in
    List.concat @@ List.mapi exprs ~f:(fun n (t,name) ->
      (* Format.printf "%a\n\n%!" Vtypes.fmt_term t; *)
      match skip_lambdas t with
      | Vtypes.Union xs ->
          List.map xs ~f:(fun (_,t) -> VHC.clause @@ hack_clause t)
      | t -> [ VHC.clause @@ hack_clause t ]
    )
  in
  VHC.pp_clauses Format.std_formatter clauses
*)


let work filename (t: Typedtree.structure) =
  Format.printf "Processing implementation file '%s'\n%!" filename;
  Printtyped.implementation Format.std_formatter t;
  Format.printf "\n\n%!";

  let api,global_effect = process_str Heap.Api.empty t in
  Format.printf "**** Final Heap\n%!";
  Format.printf "%a\n\n%!" Vtypes.fmt_heap global_effect;
  Format.printf "**** Final API\n%!";
  Format.printf "%a\n\n%!" Vtypes.fmt_api Heap.Api.(api.api);

  let props = get_properies t in
  Format.printf "+++++ Typing %d properties\n%!" (List.length props);
  let ty_prop_exprs = List.map props ~f:(fun (loc, si, _name) ->
    let (tstr, _tsgn, _, _newenv) = Typemod.type_structure t.str_final_env [si] loc in
    match tstr.str_items with
    | [{str_desc=(Tstr_eval (e,_))}] ->
        let (api, heap, term) = process_expr (api,global_effect) e in
        (* TODO: check that API didn't change *)
        (* TODO: check that not new effects appeared *)
        (term, _name)
    | _ -> failwiths "Should not happen: property representation wrong (%s %d)" __FILE__ __LINE__
  ) in
  (* REMARK: we use _old_ API here *)
  (*  let () = hornize api ty_prop_exprs in*)
  Format.printf "+++++ camlizing\n%!";
  let () = ToCaml.exec api ty_prop_exprs in
  ()
