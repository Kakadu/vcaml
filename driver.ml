open Base
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

let i_to_longi i = Longident.Lident (Ident.name i)

let rec process_str { str_items } =
  List.fold_left ~f:process_si ~init:Heap.empty str_items
and process_si heap { str_desc } =
  match str_desc with 
| Tstr_value (recflg, [vb]) -> begin 
    match process_vb heap vb with 
    | (Some lident, ans, h) -> Heap.cmps h (Heap.single lident ans)
    | _ -> assert false 
  end
| Tstr_value (recflg, vbs) -> assert false
| _ -> assert false
and process_vb heap { vb_pat; vb_expr } : Longident.t option * Heap.term * Heap.t =
  (* returns maybe identifier, 
   * rhs effect, 
   * effect thats is created by binding creation *)
  match vb_pat.pat_desc with
  | Tpat_var (ident,_) ->
      let ans,h = process_expr heap vb_expr in
      (Some (i_to_longi ident), h, ans)
  | Tpat_tuple _
  | _ -> failwith "not implemented"
and process_expr (heap : Heap.t) e =
  match e.exp_desc with
  | Texp_constant (Asttypes.Const_int n) -> (heap, Heap.CInt n)
  | Texp_construct ({txt=Lident "()"},_,[]) -> (heap, Heap.Unit)
  | Texp_ident (_,{txt=ident},_) ->
    (heap, Heap.li heap ident)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_construct({txt=Lident "()"},_,[])}; c_rhs}] } ->
    let h, ans = process_expr heap c_rhs in 
    (h, Heap.lambda None Heap.empty ans)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_var(argi,_)}; c_rhs}] } ->
    let h, ans = process_expr heap c_rhs in 
    (h, Heap.lambda (Some (i_to_longi argi)) Heap.empty ans)
  | Texp_let (_recflg, [vb], body) -> begin
      match process_vb heap vb with 
      | (Some ident, rhs, h1) -> 
          let h3, ans = process_expr h1 body in
          let h2 = Heap.cmps h1 (Heap.single ident rhs) in
          (Heap.cmps h2 h3, ans)
      | _ -> assert false 
  end
  | Texp_let (_recflg, _vbs, _body) -> assert false
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "ref"},_)}, [(_,Some e)])
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Ldot(Lident _, "ref")},_)}, [(_,Some e)]) ->
    process_expr heap e
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "<="},_)}, [(_,Some l); (_,Some r) ]) ->
    let h1,l2 = process_expr heap l in 
    let h2,r2 = process_expr h1 r in 
    ( h2
    , Heap.(binop LT) l2 r2)
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "+"},_)}, [(_,Some l); (_,Some r) ]) ->
    let h1,l2 = process_expr heap l in 
    let h2,r2 = process_expr h1 r in 
    ( h2, Heap.binop Heap.Plus l2 r2)
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "-"},_)}, [(_,Some l); (_,Some r) ]) ->
    let h1,l2 = process_expr heap l in 
    let h2,r2 = process_expr h1 r in 
    (h2, Heap.(binop Minus) l2 r2)
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident ":="},_)}, [(_,Some {exp_desc=Texp_ident(_,{txt=ident},_)}); (_,Some r) ]) ->
    let h1,r1 = process_expr heap r in 
    (Heap.cmps h1 (Heap.single ident r1), Heap.Unit)
  | Texp_apply ({exp_desc=Texp_ident(_,ident,_)}, [(_,Some e)]) ->
    let h,ans = process_expr heap e in
    (h, Heap.call ident.txt ans)
  | Texp_sequence (a,b) ->
    let h1,___ = process_expr heap a in
    let h2,ans = process_expr h1 b in
    (h2, ans)
  | Texp_ifthenelse (econd,ethen,Some eelse) -> 
    let (h1, e) = process_expr heap econd in 
    let (h2,th) = process_expr h1   ethen in 
    let (h3,el) = process_expr h2   eelse in 
    let g = (Heap.pf_term e) in 
    let notg = Heap.pf_not g in 
    (Heap.merge2     g ( h2)
                  notg ( h3)
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
  let h = process_str t in
  Sexplib.Sexp.output_hum_indent 2 stdout @@ Heap.sexp_of_t h;
  ()
