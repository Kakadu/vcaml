open Base

module type HornAPI =  sig
  type clause
  type formula
  type term
  type sort

  val clause : ?head:formula -> formula list -> clause

  module T : sig
    val int  : int ->  term
    val bool : bool -> term
    val minus : term -> term -> term
    val plus  : term -> term -> term
    val var  : string -> term
    val call_uf : string -> term list -> term
  end

  module F : sig
    val le : term -> term -> formula
    val ge : term -> term -> formula
    val lt : term -> term -> formula
    val gt : term -> term -> formula

    val eq : term -> term -> formula
    val neg : formula -> formula
    val call_rel : string -> term list -> formula
  end

  module S : sig
    val int : sort
  end

  val pp_clauses : Format.formatter -> clause list -> unit
end

type varname = int

type index_state = { mutable st_last_index : int }

let make_st () = { st_last_index = 1}
let last_index st = st.st_last_index
let new_index st =
  st.st_last_index <- st.st_last_index+1;
  last_index st


let app_space fmt pp = pp fmt; Format.fprintf fmt " "

module V1 = struct
  type formula = Format.formatter -> unit
  type term = Format.formatter -> unit
  type sort = Format.formatter -> unit

  (* TODO: can Horn Clause has empty list of premises? *)
  type clause = formula option * formula list

  let clause ?head fs = (head, fs)

  module T = struct
    let int  n fmt = Format.fprintf fmt "%d" n
    let bool b fmt = Format.fprintf fmt "%b" b
    let var  s fmt = Format.fprintf fmt "%s" s

    let binop name l r fmt =
      Format.fprintf fmt "@[(%s@ " name;
      app_space fmt l;
      r fmt;
      Format.fprintf fmt ")@]"

    let plus = binop "+"
    let minus  = binop "-"

    let call_uf s xs fmt =
      Format.fprintf fmt "@[(%s " s;
      List.iter xs ~f:(fun f  -> f fmt; Format.fprintf fmt "@ ");
      Format.fprintf fmt ")@]@ "
  end

  module F = struct
    let binop op l r fmt =
      Format.fprintf fmt "@[(%s@ " op;
      l fmt;
      Format.fprintf fmt "@ ";
      r fmt;
      Format.fprintf fmt ")@]"

    let eq = binop "="
    let le = binop "<="
    let ge = binop ">="
    let gt = binop ">"
    let lt = binop "<"

    let neg f fmt =
      Format.fprintf fmt "@[(not@ ";
      f fmt;
      Format.fprintf fmt ")@]"

    let call_rel name xs fmt =
      Format.fprintf fmt "(%s " name;
      List.iter xs ~f:(fun f  -> f fmt);
      Format.fprintf fmt ") "
  end

  let app_space fmt pp = pp fmt; Format.fprintf fmt " "

(*  let declare_rel name sorts = fun fmt ->
    Format.fprintf fmt "(declare-rel %s (" name;
    assert (List.length sorts > 0);
    List.iter sorts ~f:(app_space fmt);
    Format.fprintf fmt ")\n"*)

  module S = struct
    let int fmt  = Format.fprintf fmt "Int"
  end

  let pp_clauses fmt clauses =
    List.iter clauses ~f:(fun (h,fs) ->
      Format.fprintf fmt "@[(rule@ @[(and@ ";
      List.iter fs ~f:(app_space fmt);
      Format.fprintf fmt ")@]@ ";
      let () = match h with
      | Some h -> h fmt
      | None -> Format.fprintf fmt "false"
      in
      Format.fprintf fmt ")@]\n"
    )
end


(* ************************************************************************** *)
(* when phormulas bubble up from terms *)

let app_space fmt pp = pp fmt; Format.fprintf fmt "@ "

let v2_state = make_st ()
let next_var () = Format.sprintf "temp%d" (new_index v2_state)

module V2 : HornAPI = struct
  type post_formula = Format.formatter -> unit
  type 'a bubbled = 'a * post_formula list

  type pre_term = Format.formatter -> unit
  type term_kind = Plain of pre_term | VarNeeded of string * pre_term list

  type formula = post_formula bubbled
  type term = term_kind bubbled
  type sort = Format.formatter -> unit

  (* TODO: can Horn Clause has empty list of premises? *)
  type clause = post_formula option * post_formula list

  let clause ?head (fs: formula list) =
    let (h, aux1) = match head with
      | Some (f, fs1) -> (Some f, fs1)
      | None          -> (None, [])
    in
    let premises = List.fold_left fs ~init:[] ~f:(fun acc (f,fs) -> f :: fs @ acc) in
    (h, aux1 @ premises)

  let bubf f xs : formula = (f,xs)
  let bubt t xs : term    = (t,xs)

  let safe_term_var s = (fun fmt -> Format.fprintf fmt "%s" s)
(*  let safe_eq l r fmt =
    Format.fprintf fmt "@[(=@ ";
    app_space fmt l;
    r fmt;
    Format.fprintf fmt ")@]"*)

  let safe_term_app name args rez : post_formula = fun fmt ->
    Format.fprintf fmt "@[(%s@ " name;
    List.iter args ~f:(app_space fmt);
    rez fmt;
    Format.fprintf fmt ")@]"

  let to_plain (kind,phs) k = match kind with
  | Plain t   -> k (t, phs)
  | VarNeeded (t,args) ->
      let v = safe_term_var @@ next_var () in
      let ph1 = safe_term_app t args v in
      k (v, ph1 :: phs)

  let prepare_terms args =
    List.fold_right args
      ~f:(fun (kind, phs) (acc_ph, acc_pp_args) ->
            to_plain (kind,phs) (fun (t,phs) -> (acc_ph @ phs, t :: acc_pp_args))
         )
      ~init:([],[])


  module F = struct
    let binop op (l: term) (r: term) =
      to_plain l (fun (l, ph1) ->
      to_plain r (fun (r, ph2) ->
        let ans fmt =
          Format.fprintf fmt "@[(%s@ " op;
          l fmt;
          Format.fprintf fmt "@ ";
          r fmt;
          Format.fprintf fmt ")@]"
        in
        bubf ans (ph1 @ ph2)
      ))
    let eq = binop "="
    let le = binop "<="
    let ge = binop ">="
    let gt = binop ">"
    let lt = binop "<"

    let neg (f, other) =
      bubf (fun fmt ->
              Format.fprintf fmt "@[(not@ ";
              f fmt;
              Format.fprintf fmt ")@]")
        other

    let call_rel name args =
      let (phormulas, pps) = prepare_terms args in
      let call fmt =
        Format.fprintf fmt "@[(%s@ " name;
        List.iter pps ~f:(app_space fmt);
        Format.fprintf fmt ")@]"
      in
      bubf call phormulas
  end

  module T = struct
    let nof x = (Plain x, [])

    let int  n = nof (fun fmt -> Format.fprintf fmt "%d" n)
    let bool b = nof (fun fmt -> Format.fprintf fmt "%b" b)
    let var  s = nof (safe_term_var s)

    let binop name l r : term =
      to_plain l (fun (l, ph1) ->
      to_plain r (fun (r, ph2) ->
        let ans fmt =
          Format.fprintf fmt "@[(%s@ " name;
          app_space fmt l;
          r fmt;
          Format.fprintf fmt ")@]"
        in
        bubt (Plain ans) (ph1 @ ph2)
      ))

    let plus = binop "+"
    let minus  = binop "-"

    let call_uf name (args: term list) : term =
      let (phormulas, pps) = List.fold_right args
        ~f:(fun t (acc_ph, acc_pp_args) ->
              to_plain t (fun (t,phs) -> (acc_ph @ phs, t :: acc_pp_args))
            )
        ~init:([],[])
      in
      assert (Int.equal (List.length pps) (List.length args) );
      (*let ans fmt =
        Format.fprintf fmt "@[(%s " s;
        List.iter pps ~f:(app_space fmt);
        Format.fprintf fmt ")@]@ "
      in*)
      bubt (VarNeeded (name, pps)) phormulas
  end

(*  let declare_rel name sorts = fun fmt ->
    Format.fprintf fmt "(declare-rel %s (" name;
    assert (List.length sorts > 0);
    List.iter sorts ~f:(app_space fmt);
    Format.fprintf fmt ")\n"*)

  module S = struct
    let int fmt  = Format.fprintf fmt "Int"
  end

  let pp_clauses fmt clauses =
    List.iter clauses ~f:(fun (h,fs) ->
      Format.fprintf fmt "@[(rule@ @[(and@ ";
      List.iter fs ~f:(app_space fmt);
      Format.fprintf fmt ")@]@ ";
      let () = match h with
      | Some h -> h fmt
      | None -> Format.fprintf fmt "false"
      in
      Format.fprintf fmt ")@]\n"
    )
end

type heap_index = string
type ident = string

module type ML_API = sig
  type program
  type expr
  type si
  module E : sig
    val gt: expr -> expr -> expr
    val ge: expr -> expr -> expr
    val eq: expr -> expr -> expr
    val int: int -> expr

    val neg: expr -> expr
    val and_: expr -> expr -> expr

    val ident: string -> expr
    val app2 : expr -> expr -> expr
    val app  : expr -> expr list -> expr
    val find : heap_index -> expr
    val switch_ident : ident -> (ident * expr) list -> expr
    val ite : expr -> expr -> expr -> expr

    val unreachable: expr
    val todo: expr
  end
  module SI : sig
    val find : string -> (string -> string -> expr) -> si
    val assert_: ?name:string -> string list -> expr -> si
  end

  val program : si list -> program
  val join_programs : program list -> program
  val pp_program : Format.formatter -> program -> unit
end

module ML : ML_API = struct
  type expr = Format.formatter -> unit
  type program = Format.formatter -> unit
  type si = Format.formatter -> unit

  module E = struct
    let binop name l r : expr =
        let ans fmt =
          Format.fprintf fmt "@[(";
          app_space fmt l;
          Format.fprintf fmt "%s@ " name;
          r fmt;
          Format.fprintf fmt ")@]"
        in
        ans

    let gt = binop ">"
    let ge = binop ">="
    let and_ = binop "&&"
    let eq = binop "="


    let app2 = binop ""
    let app f = function
      | [] -> f
      | xs -> List.fold_left xs ~init:f ~f:app2
    let int n fmt = Format.fprintf fmt "%d" n
    let ident s fmt = Format.fprintf fmt "%s" s
    let find str_ndx fmt =
      Format.fprintf fmt "find_%s" str_ndx

    let konst f = fun fmt () -> f fmt
    let neg f fmt = Format.fprintf fmt "@[(not %a)@]" (konst f) ()

    let switch_ident scru cases fmt =
      Format.fprintf fmt "@[<hov 2>(";
      List.iter cases ~f:(fun (id,e) ->
        Format.fprintf fmt "@[if %s = %s@ @]"
          scru id;
        Format.fprintf fmt "@[then@ @]";
        e fmt;
        Format.fprintf fmt "@[@ else@ @]";
      );
      Format.fprintf fmt "@[else failwith \"unreachable\")@]";
      Format.fprintf fmt "@]"

    let ite c th el fmt =
      Format.fprintf fmt "(if %a then %a else %a)" (konst c) () (konst th) () (konst el) ()

    let unreachable fmt =
(*      Format.fprintf fmt "(failwith (Printf.sprintf \"unreachable %%s %%d\" __FILE__ __LINE__))"*)
      Format.fprintf fmt "(failwith \"unreachable\""
    let todo fmt = Format.fprintf fmt "TODO"
  end

  module SI = struct
    let find name body fmt =
      let tau = "tau" in
      let x = "x" in
      Format.fprintf fmt "@[let@ find_%s@ =@ fun %s %s -> " name tau x;
      body tau x fmt;
      Format.fprintf fmt "@]"

    let assert_ ?name vars expr fmt =
      Format.fprintf fmt "@[let@ assert";
      Base.Option.iter name ~f:(Format.fprintf fmt "_%s");
      Format.fprintf fmt "@ " ;
      List.iter vars ~f:(Format.fprintf fmt "%s@ ");
      Format.fprintf fmt "=@ ";
      expr fmt;
      Format.fprintf fmt "@]"

  end

  let program es fmt =
    List.iter es ~f:(fun pp -> pp fmt; Format.fprintf fmt "\n");
    Format.fprintf fmt "%!"
  let join_programs es fmt =
      List.iter es ~f:(fun pp -> pp fmt; Format.fprintf fmt "\n");
      Format.fprintf fmt "%!"

  let pp_program fmt pp = pp fmt
end
