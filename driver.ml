open Base
open Printf
open Typedtree

module UntypeP = struct
  let expr e =
    let b = Buffer.create 20 in
    let fmt = Format.formatter_of_buffer b in
    Untypeast.default_mapper.expr Untypeast.default_mapper e |> Printast.expression 0 fmt;
    Format.pp_print_flush fmt ();
    Buffer.contents b

end

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

let failwiths = Heap.failwiths

let find_lident api heap ident =
  match Heap.Api.is_pending api ident with
  | true -> Heap.li ~heap ident
  | false ->
      match Heap.Api.find_ident_exn api ident with
      | term -> term
      | exception Not_found -> failwiths "find_lident: can't find on ident '%a'" Heap.MyIdent.pp_string ident

let rec process_str api { str_items; _ } : Heap.Api.t * Heap.t =
  List.fold_left ~f:process_si ~init:(api, Heap.hempty) str_items
and process_si (api,heap) { str_desc; _} : Heap.Api.t * Heap.t =
  match str_desc with
| Tstr_value (recflg, [vb]) -> begin
    match process_vb (api,heap) recflg vb with
    | (Some ident, ans, h) ->
        ( Heap.Api.add api ident ans
        , Heap.hcmps heap h)
    | _ -> assert false
  end
| Tstr_value (recflg, vbs) -> assert false
| _ -> assert false
and process_vb (api,heap) recflg { vb_pat; vb_expr; _ } : Heap.MyIdent.t option * Heap.term * Heap.t =
  (* returns maybe identifier,
   * rhs effect,
   * effect thats is created by binding creation *)
  (* Format.eprintf "process_vb: ... = '%s'\n%!" (UntypeP.expr vb_expr); *)
  match vb_pat.pat_desc with
  | Tpat_var (ident,_) ->
      let api = match recflg with
        | Nonrecursive -> api
        | Recursive -> Heap.Api.add (Heap.Api.add_pending api ident) ident (Heap.li ident)
      in
      let (_new_api,ans,h) = process_expr (api,heap) vb_expr in
      (Some ident, h, ans)
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
  | Texp_constant (Asttypes.Const_int n) -> (api, Heap.hempty, Heap.CInt n)
  | Texp_construct ({txt=Lident "()"},_,[]) -> (api, Heap.hempty, Heap.Unit)
  | Texp_ident (Pident ident,{txt=lident},_) ->
    (* TODO: use path here *)
    (* identifiers are returned as is. No inlining yet, even for functions *)
    (api, heap, find_lident api heap ident)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_construct({txt=Lident "()"},_,[])}; c_rhs}] } ->
        (* Processing `fun () -> c_rhs` *)
    let api, h, ans = process_expr (api,heap) c_rhs in
    (api, Heap.hempty, Heap.lambda false None (fst api) h ans)

  | Texp_function { param; cases=[{c_guard=None; c_lhs={pat_desc=Tpat_var(argname,_)}; c_rhs}] } ->
        (* Processing `fun argname -> c_rhs` *)
      let api = Heap.Api.add api param (Heap.li param) in
      let api, h, ans = process_expr (api,heap) c_rhs in
      (api, Heap.hempty, Heap.lambda false (Some argname) (fst api) h ans)

  | Texp_let (_recflg, [vb], body) -> begin
      match process_vb (api,heap) _recflg vb with
      | (Some ident, rhs, heff) ->
          (* we don't care about isolation here, so we compose heaps with toplevel one *)
          let heap = Heap.hcmps heap heff in
          let heap = Heap.hcmps heap (Heap.hsingle ident rhs) in
          (* we need to extend API before processing the body *)
          let api = Heap.Api.add api ident rhs in
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
    let op = match opname with
      | "<=" -> Heap.LE
      | "<"  -> Heap.LT
      | ">"  -> Heap.GT
      | "+"  -> Heap.Plus
      | "-"  -> Heap.Minus
      | _ -> failwiths "not supported (weakly typed code): '%s'" opname
    in
    (* Although we don't need to return updated API we return it
     * to have a global cache of function summaries *)
    let api_1,h1,l2 = process_expr (api,heap) l in
    let api_2,h2,r2 = process_expr (api_1,h1) r in
    (api_2, h2, Heap.binop op l2 r2)
  end
  | Texp_apply ({exp_desc=Texp_ident(Pdot (Pident _ident,":=",_), _, _)},
               [(_,Some {exp_desc=Texp_ident(Pident ident,_,_)}); (_,Some rhs) ]) -> begin
        (* ident := rhs *)
    (* Format.eprintf "Tracing '%s'" (UntypeP.expr e); *)
    let api_1,h1,r1 = process_expr (api,heap) rhs in
    let heap_ans = Heap.hcmps h1 (Heap.hsingle ident r1) in
    (api_1, heap_ans, Heap.Unit)
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
  | Texp_apply ({exp_desc=Texp_ident(Pident ident,_,_)}, [(_,Some e)]) -> begin
    (* Now: real function application *)
    let api,argeff,ans = process_expr (api,heap) e in
    (* now we need to compose effect of e with effect of call
       But for recursive calls -- we shouldn't
     *)
    match find_lident api heap ident with
    | Heap.Lambda { lam_is_rec=true; _ } ->
        Format.eprintf "%s %d\n%!" __FILE__ __LINE__;
        (* recursive functions we left as is *)
        (api, Heap.hcmps argeff (Heap.hcall (Heap.li ident) ans), Heap.call (Heap.li ~heap ident) ans)
    | Heap.Lambda {lam_argname; lam_eff; lam_api; lam_body} ->
        Format.eprintf "%s %d\n%!" __FILE__ __LINE__;
        (* Let's not inline recursive functions too *)
        (api, Heap.hcmps argeff (Heap.hcall (Heap.li ident) ans), Heap.call (Heap.li ~heap ident) ans)
        (* let app_eff = Heap.heap_subst argeff lam_argname ans in
        (api, app_eff, Heap.call (Heap.li ~heap ident) ans) *)
    | Heap.LI (h, ident) as func ->
        Format.eprintf "%s %d\n%!" __FILE__ __LINE__;
        (api, Heap.hcmps argeff (Heap.hcall (Heap.li ident) ans), Heap.call func ans)
    | exception Not_found -> failwith (Printf.sprintf "Identifier unbound: '%a'" Heap.MyIdent.pp_string ident)
    | ans_term ->
        failwith (sprintf "typecheck error? should not happed. Searched for ident %a. Got '%a'"
                    Heap.MyIdent.pp_string ident
                    Heap.pp_term ans_term
                )
  end
  | Texp_sequence (a,b) ->
    let api,effa,___ = process_expr (api,heap) a in
    let api,effb,ans = process_expr (api,heap) b in
    (api, Heap.hcmps effa effb, ans)
  | Texp_ifthenelse (econd, ethen, Some eelse) ->
    let (api,h1, e) = process_expr (api,heap) econd in
    let h_after_cond = h1 in
    let (api,h2,th) = process_expr (api,h_after_cond) ethen in
    let (api,h3,el) = process_expr (api,h_after_cond) eelse in
    let g    = Heap.pf_term e in
    let notg = Heap.pf_not g in
    (api, Heap.hmerge2     g h2 notg h3, Heap.union2 g th notg el)
  | Texp_match (what, cases, _exc_cases, _) -> begin
    Format.eprintf "HERR\n%!";

    match cases with
    | [{c_lhs={pat_desc=Tpat_construct ({txt=Lident "()"},_,[])}; c_rhs}] ->
        let api, eff, _scrut = process_expr (api,heap) what in
        process_expr (api,eff) c_rhs
    | _ -> assert false
  end
  | _ -> failwith ("not implemented " ^ UntypeP.expr e)


let work { Misc.sourcefile = filename } (t: Typedtree.structure) =
  Format.pp_set_margin Format.std_formatter 150;
  Format.printf "Processing implementation file '%s'\n%!" filename;
  Printtyped.implementation Format.std_formatter t;
  Format.printf "\n\n%!";

  let api,h = process_str (Heap.Api.empty) t in
  Format.printf "%a\n\n%!" Heap.fmt_heap h;
  Format.printf "%a\n\n%!" Heap.fmt_api (fst api);
  ()
