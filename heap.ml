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
              method fmt fmt o = Format.fprintf fmt "<someident>"
          end
          ; GT.fix = (fun _ -> assert false)
          }
end

(* type cre_mode = Assign | Const [@@deriving gt ~options:{ fmt }] *)
let pp_longident () lident = Longident.flatten lident |> String.concat ~sep:"."
type term = LI of heap GT.option * MyIdent.t
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
and api = (MyIdent.t * term) GT.list [@@deriving gt ~options:{ fmt }]
(* TODO: it should be path here *)
and t = HAssoc of (MyIdent.t * term) GT.list
        (* Heap should be a mapping from terms to terms (array access, for example)
         * but for fibonacci it doesn't matter
         *)
      | HMerge of (pf * t) GT.list
      | HCmps of heap * heap
      | HCall of term * term
      | HEmpty
[@@deriving gt ~options:{ fmt }]
and pf  = LogicBinOp of logic_op * pf * pf
        | Not of pf
        | EQident of MyIdent.t * MyIdent.t
        | PFTrue
        | PFFalse
        | Term of term
[@@deriving gt ~options:{ fmt }]
and logic_op = Conj | Disj [@@deriving gt ~options:{ fmt }]
and op = | Plus | Minus | LT | LE | GT | GE | Eq [@@deriving gt ~options:{ fmt }]
and heap = t [@@deriving gt ~options:{ fmt }]
let pp_term () t = Sexplib.Sexp.to_string @@ sexp_of_term t
let pp_heap () h = Sexplib.Sexp.to_string @@ sexp_of_heap h

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
