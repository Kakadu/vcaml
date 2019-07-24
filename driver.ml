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
  List.fold_left ~f:(fun acc x -> Heap.cmps (process_si x) acc) ~init:Heap.empty str_items
and process_si { str_desc } = process_si_desc str_desc
and process_si_desc : _ -> Heap.t = function
| Tstr_value (recflg, [vb]) ->
  process_vb vb
| Tstr_value (recflg, vbs) ->  assert false
| _ -> assert false
and process_vb { vb_pat; vb_expr } : Heap.t =
  match vb_pat.pat_desc with
  | Tpat_tuple xs -> Heap.empty
  | Tpat_var (ident,_) ->
      let h,ans = process_expr vb_expr in
      Heap.cmps h (Heap.single (i_to_longi ident) ans)

  | _ -> failwith "not implemented"
and process_cond_expr e = match e.exp_desc with
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "<="},_)}, [(_,Some l); (_,Some r) ]) ->
    Heap.BinOp
  | _ -> failwith ("not implemented " ^ UntypeP.expr e)
and process_expr e =
  match e.exp_desc with
  | Texp_constant (Asttypes.Const_int n) -> (Heap.empty, Heap.CInt n)
  | Texp_construct ({txt=Lident "()"},_,[]) -> (Heap.empty, Heap.Unit)
  | Texp_ident (_,{txt=ident},_) ->
    (Heap.empty, Heap.li ident)
  | Texp_function { cases=[{c_guard=None; c_lhs={pat_desc=Tpat_var(argi,_)}; c_rhs}] } ->
    process_expr c_rhs
  | Texp_let (recflg, [vb], body) -> begin
    let h1 = process_vb vb in
    let h2, ans = process_expr body in
    (Heap.cmps h1 h2, ans)
  end
  | Texp_let (_recflg, _vbs, _body) -> assert false
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Lident "ref"},_)}, [(_,Some e)])
  | Texp_apply ({exp_desc=Texp_ident(_,{txt=Ldot(Lident _, "ref")},_)}, [(_,Some e)]) ->
    process_expr e
  | Texp_apply ({exp_desc=Texp_ident(_,ident,_)}, [(_,Some e)]) ->
    let h,ans = process_expr e in
    (h, Heap.call ident.txt ans)
  | Texp_sequence (a,b) ->
    let h1,___ = process_expr a in
    let h2,ans = process_expr b in
    (Heap.cmps h1 h2, ans)
  | Texp_ifthenelse (econd,ethen,_) -> process_expr ethen

  | _ -> failwith ("not implemented " ^ UntypeP.expr e)


let work { Misc.sourcefile = filename } (t: Typedtree.structure) =
  Format.printf "Processing implementation file '%s'\n%!" filename;
  Printtyped.implementation Format.std_formatter t;
  let h = process_str t in
  ()
