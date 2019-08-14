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

let (%%%) = Heap.hcmps
(* let is_arr expr =
  match expr.exp_type.Types.desc with
  | Tarrow (_,_,_,_) -> true
  | _ -> false *)

(* let i_to_longi i = Longident.Lident (Ident.unique_name i) *)

(* let standart_heap = Heap.hempty *)
  (* Heap.single (Lident "!") (Heap.lambda (Some (Lident "x")) Heap.empty (Heap.li (Heap.empty) (Lident "x"))) *)

let is_binop = function
  | "<=" | "<" | ">" | ">=" | "+" | "-"  -> true
  | _ -> false

exception IdentNotFound of MyIdent.t  * string
let ident_not_found ident fmt =
  Format.ksprintf (fun s -> raise (IdentNotFound (ident,s))) fmt

let find_lident api heap ident typ =
  match Heap.Api.is_pending api ident with
  | true -> Heap.li ~heap ident typ
  | false ->
      match Heap.Api.find_ident_exn api ident with
      | (_,term) -> term
      | exception Not_found -> ident_not_found ident "find_lident: can't find on ident '%a'" MyIdent.pp_string ident

let rec process_str api { str_items; _ } : Heap.Api.t * Vtypes.t =
  List.fold_left ~f:process_si ~init:(api, Heap.hempty) str_items
and process_si (api,heap) { str_desc; _} : Heap.Api.t * Vtypes.t =
  match str_desc with
  | Tstr_value (recflg, [vb]) -> begin
    match process_vb (api, Heap.hempty) recflg vb with
    | (api, Some ident, ans, heff) ->
        ( Heap.Api.add api ident (recflg, ans)
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
            Heap.Api.add_pending api ident
      in
      let (api,eff,ans) = process_expr (api, Heap.hempty) vb_expr in
      FCPM.is_caml_ref vb_expr
        ~ok:(fun _ ->
              (api, Some ident, ans, heap %%% eff %%% Heap.(hsingle ident ans))
          )
        (fun () -> (api, Some ident, ans, heap %%% eff) )
      (* (api, Some ident, ans, heap %%% eff) *)
  | _ -> failwith "not implemented"

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
    (api, heap, Heap.li ident val_type)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_construct({txt=Lident "()"},_,[])}; c_rhs}] } ->
        (* Processing `fun () -> c_rhs` *)
    let api, h, ans = process_expr (api,heap) c_rhs in
    (* Format.eprintf "%s %d %a\n%!" __FILE__ __LINE__ Vtypes.t.GT.plugins#fmt h; *)
    (api, Heap.hempty, Heap.lambda false None (fst api) h ans e.exp_type)

  | Texp_function { param; cases=[{c_guard=None; c_lhs={pat_desc=Tpat_var(argname,_)}; c_rhs}] } ->
        (* Processing `fun argname -> c_rhs` *)
      (* let api = Heap.Api.add api param (Heap.li param) in *)
      let api, h, ans = process_expr (api,heap) c_rhs in

      (* Format.eprintf "%s %d %a\n%!" __FILE__ __LINE__ Vtypes.t.GT.plugins#fmt h; *)
      (api, Heap.hempty, Heap.lambda false (Some argname) (fst api) h ans e.exp_type)

  | Texp_let (recflg, [vb], body) -> begin
      match process_vb (api,heap) recflg vb with
      | (api, Some ident, rhs, heff) ->
          (* we don't care about isolation here, so we compose heaps with toplevel one *)
          let heap = Heap.hcmps heap heff in
          let heap = Heap.hcmps heap (Heap.hsingle ident rhs) in
          (* we need to extend API before processing the body *)
          let api = Heap.Api.add api ident (recflg,rhs) in
          let api, heff3, ans = process_expr (api,heap) body in
          (api, heff3, ans)
      | _ -> assert false
  end
  | Texp_let (_recflg, _vbs, _body) -> assert false

  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "ref"},_)}, [(_,Some e)])
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Ldot(Lident _, "ref")},_)}, [(_,Some e)]) ->
      (* Do we need explicit derefenrecing? *)
      process_expr (api, heap) e
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident opname},_)}, [(_,Some l); (_,Some r) ])
        when is_binop opname -> begin
    (* binop *)
    let op,rez_typ = match opname with
      | "<=" -> Vtypes.LE, Predef.type_bool
      | "<"  -> Vtypes.LT, Predef.type_bool
      | ">"  -> Vtypes.GT, Predef.type_bool
      | ">=" -> Vtypes.GE, Predef.type_bool
      | "+"  -> Vtypes.Plus,  Predef.type_int
      | "-"  -> Vtypes.Minus, Predef.type_int
      | _ -> failwiths "not supported (weakly typed code): '%s'" opname
    in
    (* Although we don't need to return updated API we return it
     * to have a global cache of function summaries *)
    let api_1,h1,l2 = process_expr (api,heap) l in
    let api_2,h2,r2 = process_expr (api_1,h1) r in
    (api_2, h2, Heap.binop op l2 r2 rez_typ)
  end
  | Texp_apply ({exp_desc=Texp_ident(Pdot (Pident _ident,":=",_), _, _)},
               [(_,Some {exp_desc=Texp_ident(Pident ident,_,_)}); (_,Some rhs) ]) -> begin
        (* ident := rhs *)
    (* Format.eprintf "Tracing '%s'" (UntypeP.expr e); *)
    let api_1,h1,r1 = process_expr (api,heap) rhs in
    (* Format.eprintf "%s %d %a\n" __FILE__ __LINE__ Vtypes.t.GT.plugins#fmt h1; *)
    let heap_ans = Heap.hcmps h1 (Heap.hsingle ident r1) in
    (api_1, heap_ans, Heap.cunit)
    (* match Heap.Api.find_ident_exn api ident with
    | Heap.LI (h,ident) ->
      let heap_ans = Heap.hcmps h1 (Heap.hsingle ident r1) in
      (* The idea is to have all optimisation operations in Heap module *)
      (api_1, heap_ans, Heap.Unit)
    | z -> failwith @@ Format.sprintf "not implemented. Expected LI but got '%a'" Heap.pp_term z *)
  end
  | Texp_apply ({exp_desc=Texp_ident(Pdot (Pident _ident, "!", _), _, _)}, [ (_,Some r) ]) -> begin
    let api,h,r = process_expr (api,heap) r in
    (api,h,r)
  end
  | Texp_apply ({exp_desc=Texp_ident(Pident ident,_,{val_type})}, [(Asttypes.Nolabel,Some arg)]) -> begin
    (* Now: real function application *)
    let api,arg_eff,arg_evaled = process_expr (api, Heap.hempty) arg in
    (* now we need to compose effect of e with effect of call
       But for recursive calls -- we shouldn't
     *)
    match find_lident api heap ident val_type with
    | exception IdentNotFound (_,_) -> begin
        (* It could be a recursive call *)
        if Heap.Api.is_pending api ident
        then (api, heap, Heap.li ident val_type)
        else failwiths "(should not happen) not implemented %s %d" __FILE__ __LINE__
    end

    | Vtypes.Lambda  _ when Heap.Api.is_pending api ident || Heap.Api.is_recursive_exn api ident ->
        (* recursive functions we left as is *)
        ( api
        , Heap.hcmps arg_eff (Heap.hcall (Heap.li ident val_type) [arg_evaled])
        , Heap.call (Heap.li ~heap ident val_type) [arg_evaled] e.exp_type)
    | Vtypes.Lambda {lam_argname; lam_eff; lam_api; lam_body} ->
        (* Format.eprintf "%s %d\n%!" __FILE__ __LINE__; *)
        (* for nonrecursive lambdas we need to compose its effect after binding the argument *)
        let argb = match lam_argname with
          | None -> Heap.hempty
          | Some argname -> Heap.hsingle argname arg_evaled
        in
        let env_h   = (heap %%% arg_eff) %%% argb in
        let app_eff = env_h %%% lam_eff in
        let app_rez = Heap.hdot env_h lam_body in
        (api, app_eff, app_rez)
        (* (api, Heap.hcmps argeff (Heap.hcall (Heap.li ident) ans), Heap.call (Heap.li ~heap ident) ans) *)
        (* let app_eff = Heap.heap_subst argeff lam_argname ans in
        (api, app_eff, Heap.call (Heap.li ~heap ident) ans) *)
    | Vtypes.LI (h, ident, typ) as func ->
        (api, Heap.hcmps arg_eff (Heap.hcall (Heap.li ident typ) [arg_evaled]), Heap.call func [arg_evaled] e.exp_type)
    (* | exception Not_found -> failwith (Printf.sprintf "Identifier unbound: '%a'" Vtypes.MyIdent.pp_string ident) *)
    | ans_term ->
        failwith (sprintf "typecheck error? should not happed. Searched for ident %a. Got '%a'"
                    Vtypes.MyIdent.pp_string ident
                    Heap.pp_term ans_term
                )
  end
  | Texp_apply ({exp_desc=Texp_ident(Pident ident,_,{val_type})}, args) -> begin
      let args = List.map args ~f:(function
        | (Asttypes.Nolabel, Some arg) -> arg
        | _ -> failwiths "labeled arguments not supported (%s %d)\n%!" __FILE__ __LINE__
      )
      in
      (* Format.printf "Got multiple (%d) arguments\n%!" (List.length args); *)
      match find_lident api heap ident val_type with
      | exception IdentNotFound (_,_) -> begin
        (* It could be a recursive call *)
        if Heap.Api.is_pending api ident
        then (api, heap, Heap.li ident val_type)
        else failwiths "(should not happen) not implemented %s %d" __FILE__ __LINE__
      end
      | Vtypes.Lambda { lam_eff; lam_body; lam_argname }
                      when Heap.Api.is_pending api ident || Heap.Api.is_recursive_exn api ident ->
        (* for recursive calls we do nothing interesting *)
        (* we evaluate from right to left (native code) and left call in the result *)
        let api, eff, evaled_args =
          List.fold_right args ~init:(api,heap,[])
            ~f:(fun arg (api,acch,rezs) ->
                  let api,arg_eff,arg_evaled = process_expr (api, Heap.hempty) arg in
                  (api, acch %%% arg_eff, arg_evaled :: rezs)
            )
        in

        ( api
        , Heap.hcmps eff (Heap.hcall (Heap.li ident val_type) evaled_args)
        , Heap.call (Heap.li ~heap ident val_type) evaled_args e.exp_type)
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
            ~init:(api, Heap.hempty, Heap.hempty, Heap.li ~heap ident val_type, lam_eff, lam_body, val_type)
            ~finish:(fun acc -> (acc,[]))
            ~f:(fun ((api, eff, arg_bindings, func, lam_eff, lam_body, typ) as theacc) hterm tl k ->
                  (* We accumulate on the go  1) an effect 2) term 3) the non-applied arguments *)
                  match lam_body with
                  | Vtypes.Lambda { lam_eff=next_eff; lam_body=next_body; lam_argname=(Some nextargname) } ->
                    let xxx1 = Heap.hsingle nextargname hterm in
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
                      (* (eff, func, lam_eff, lam_body) *)
                )
          in
          (match fuck with
          | ((api,acced_eff,_,term_rez,_,_, typ), xs) ->
              (* recursive functions we left as is *)
              ( api
              , heap %%% all_args_eff %%% acced_eff
              , Heap.call term_rez xs typ)
          (* | (_,xs) ->
           *     Format.printf "Got non-apllied arguments: \n%!";
           *     List.iter xs ~f:(fun e -> Format.printf "\t%s\n%!" (UntypeP.expr e) );
           *     failwiths "not implemented on %s %d" __FILE__ __LINE__ *)
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
        , Heap.call func evaled_args e.exp_type)
      | _ -> assert false

  end
  | Texp_sequence (a,b) ->
    let api,effa,___ = process_expr (api,Heap.hempty) a in
    let api,effb,ans = process_expr (api,Heap.hempty) b in
    (api, heap %%% effa %%% effb, ans)
  | Texp_ifthenelse (econd, ethen, Some eelse) ->
    let (api,h1, e) = process_expr (api,heap) econd in
    let h_after_cond = h1 in
    let (api,h2,th) = process_expr (api,h_after_cond) ethen in
    let (api,h3,el) = process_expr (api,h_after_cond) eelse in
    let g    = Heap.pf_term e in
    let notg = Heap.pf_not g in
    (api, Heap.hmerge2     g h2 notg h3, Heap.union2 g th notg el)
  | Texp_match (what, cases, _exc_cases, _) -> begin
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


let work { Misc.sourcefile = filename } (t: Typedtree.structure) =
  let () =
    let sz = Option.value ~default:170 (Terminal_size.get_columns ()) in
    Format.printf "terminal with = %d\n%!" sz;
    Format.pp_set_margin Format.std_formatter (sz-1);
    Format.pp_set_max_indent Format.std_formatter 2000 (* (sz-1) *)
  in
  Format.printf "Processing implementation file '%s'\n%!" filename;
  Printtyped.implementation Format.std_formatter t;
  Format.printf "\n\n%!";

  let api,h = process_str Heap.Api.empty t in
  Format.printf "**** Final Heap\n%!";
  Format.printf "%a\n\n%!" Vtypes.fmt_heap h;
  Format.printf "**** Final API\n%!";
  Format.printf "%a\n\n%!" Vtypes.fmt_api (fst api);
  ()
