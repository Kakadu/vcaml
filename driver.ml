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

let is_arr expr =
  match expr.exp_type.Types.desc with
  | Tarrow (_,_,_,_) -> true
  | _ -> false

let i_to_longi i = Longident.Lident (Ident.unique_name i)

let standart_heap = Heap.empty
  (* Heap.single (Lident "!") (Heap.lambda (Some (Lident "x")) Heap.empty (Heap.li (Heap.empty) (Lident "x"))) *)

let is_binop = function 
  | "<=" | "<" | ">" | ">=" | "+" | "-"  -> true 
  | _ -> false 

let find_ident api heap lident = 
  Heap.hfind_li heap lident

let rec process_str api { str_items; _ } : Heap.Api.t * Heap.t =
  List.fold_left ~f:process_si ~init:(api,Heap.empty) str_items
and process_si (api,heap) { str_desc; _} : Heap.Api.t * Heap.t =
  match str_desc with 
| Tstr_value (recflg, [vb]) -> begin 
    match process_vb (api,heap) vb with 
    | (Some lident, ans, h) -> 
        ( Heap.Api.add api lident ans 
        , Heap.cmps heap h)
    | _ -> assert false 
  end
| Tstr_value (recflg, vbs) -> assert false
| _ -> assert false
and process_vb (api,heap) _recflg { vb_pat; vb_expr; _ } : Longident.t option * Heap.term * Heap.t =
  (* returns maybe identifier, 
   * rhs effect, 
   * effect thats is created by binding creation *)
  (* let api1 = Api.add_pending api *)
  match vb_pat.pat_desc with
  | Tpat_var (ident,_) ->
      let (_new_api,ans,h) = process_expr (api,heap) vb_expr in
      (Some (i_to_longi ident), h, ans)
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
  | Texp_constant (Asttypes.Const_int n) -> (api, Heap.empty, Heap.CInt n)
  | Texp_construct ({txt=Lident "()"},_,[]) -> (api, Heap.empty, Heap.Unit)
  | Texp_ident (_,{txt=ident},_) ->
    (* identifiers are returned as is. No inlining yet, even for functions *)
    (api, Heap.empty, find_ident api heap ident)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_construct({txt=Lident "()"},_,[])}; c_rhs}] } ->
        (* Processing `fun () -> c_rhs` *)
    let api, h, ans = process_expr (api,heap) c_rhs in 
    (api, Heap.empty, Heap.lambda None api h ans)

  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_var(argname,_)}; c_rhs}] } ->
        (* Processing `fun argname -> c_rhs` *)
    let api, h, ans = process_expr (api,heap) c_rhs in 
    (api, Heap.empty, Heap.lambda (Some (i_to_longi argname)) api h ans)

  | Texp_let (_recflg, [vb], body) -> begin
      match process_vb (api,heap) _recflg vb with
      | (Some ident, rhs, heff) ->
          (* we don't care about isolation here, so we compose heaps with toplevel one *)
          let heff2 = Heap.cmps heap heff in 
          (* we need to extend API before processing the body *)
          let api1 = Api.add api ident rhs in
          let api2, heff3, ans = process_expr (api1,heff2) body in
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
      | _ -> failwith "not supported (weakly typed code)" 
    in 
    (* Although we don't need to return updated API we return it 
     * to have a global cache of function summaries *)
    let api_1,h1,l2 = process_expr (api,heap) l in 
    let api_2,h2,r2 = process_expr (api_1,h1) r in 
    (api_2, h2, Heap.binop op l2 r2)
  end
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident ":="},_)}, [(_,Some {exp_desc=Texp_ident(_,{txt=ident},_)}); (_,Some r) ]) ->
    let api_1,h1,r1 = process_expr (api,heap) r in 
    let heap_ans = Heap.cmps h1 (Heap.single ident r1) in 
    (* The idea is to have all optimisation operations in Heap module *)
    (api_1, heap_ans, Heap.Unit)

  | Texp_apply ({exp_desc=Texp_ident(_,{txt=ident},_)}, [(_,Some e)]) -> begin 
    (* Now: real function application *)
    let api,argeff,ans = process_expr (api,heap) e in    
    (* now we need to compose effect of e with effect of call
       But for recursive calls -- we shouldn't
     *)
    match find_ident api heap ident with 
    | Heap.Lambda {lam_argname; lam_eff; lam_api; lam_body} -> 
        (api, argeff, Heap.call (Heap.li heap ident) ans)
    | Heap.LI (h, ident) as func -> (argeff, Heap.call func ans) 
    | exception Not_found -> failwith (Printf.sprintf "Identifier unbound: '%s'" (Heap.Longident.to_string ident))
    | ans_term -> 
        failwith (sprintf "typecheck error? should not happed. Searched for ident %a. Got '%a'" 
                    Heap.Longident.pp_string ident
                    Heap.pp_term ans_term
                )
  end
  | Texp_sequence (a,b) ->
    let effa,___ = process_expr heap a in
    let effb,ans = process_expr heap b in
    (Heap.cmps effa effb, ans)
  | Texp_ifthenelse (econd,ethen,Some eelse) -> 
    let (h1, e) = process_expr heap econd in
    let h_after_cond = h1 in 
    let (h2,th) = process_expr h_after_cond   ethen in 
    let (h3,el) = process_expr h_after_cond   eelse in 
    let g    = Heap.pf_term e in 
    let notg = Heap.pf_not g in 
    (Heap.merge2     g h2
                  notg h3
    , Heap.union2 g th notg el)
  | Texp_match (what, cases, _exc_cases, _) -> begin 
    match cases with 
    | [{c_lhs={pat_desc=Tpat_construct ({txt=Lident "()"},_,[])}; c_rhs}] -> process_expr heap c_rhs
    | _ -> assert false 
  end 
  | _ -> failwith ("not implemented " ^ UntypeP.expr e)


let work { Misc.sourcefile = filename } (t: Typedtree.structure) =
  Format.pp_set_margin Format.std_formatter 100;
  Format.printf "Processing implementation file '%s'\n%!" filename;
  Printtyped.implementation Format.std_formatter t;
  let h = process_str standart_heap t in
  Sexplib.Sexp.output_hum_indent 2 stdout @@ Heap.sexp_of_t h;
  ()
