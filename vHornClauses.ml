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

  let declare_rel name sorts = fun fmt ->
    Format.fprintf fmt "(declare-rel %s (" name;
    assert (List.length sorts > 0);
    List.iter sorts ~f:(app_space fmt);
    Format.fprintf fmt ")\n"

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

  type term_kind = Plain | VarNeeded
  type pre_term = Format.formatter -> unit

  type formula = post_formula bubbled
  type term = (pre_term * term_kind) bubbled
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
  let bubt t k xs : term = ((t,k),xs)

  let safe_term_var s = (fun fmt -> Format.fprintf fmt "%s" s)
  let safe_eq l r fmt =
    Format.fprintf fmt "@[(=@ ";
    app_space fmt l;
    r fmt;
    Format.fprintf fmt ")@]"

  let to_plain (((t,kind),phs): term) k = match kind with
  | Plain     -> k (t, phs)
  | VarNeeded ->
      let v = safe_term_var @@ next_var () in
      let ph1 = safe_eq v t in
      k (v, ph1 :: phs)

  let prepare_terms args =
    List.fold_right args
      ~f:(fun ((t, kind), phs) (acc_ph, acc_pp_args) ->
          match kind with
          | Plain     -> (acc_ph @ phs, t :: acc_pp_args)
          | VarNeeded ->
              let v = safe_term_var @@ next_var () in
              let ph1 = safe_eq v t in
              (acc_ph @ phs @ [ph1], v :: acc_pp_args)
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
    let nof x = ((x, Plain), [])

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
        bubt ans Plain (ph1 @ ph2)
      ))

    let plus = binop "+"
    let minus  = binop "-"

    let call_uf s args : term =
      let (phormulas, pps) = List.fold_right args
        ~f:(fun ((t, kind), phs) (acc_ph, acc_pp_args) ->
            match kind with
            | Plain     -> (acc_ph @ phs, t :: acc_pp_args)
            | VarNeeded ->
                let v = safe_term_var @@ next_var () in
                let ph1 = safe_eq v t in
                (acc_ph @ phs @ [ph1], v :: acc_pp_args)
            )
        ~init:([],[])
      in
      assert (Int.equal (List.length pps) (List.length args) );
      let ans fmt =
        Format.fprintf fmt "@[(%s " s;
        List.iter pps ~f:(app_space fmt);
        Format.fprintf fmt ")@]@ "
      in
      bubt ans VarNeeded phormulas
  end

  let declare_rel name sorts = fun fmt ->
    Format.fprintf fmt "(declare-rel %s (" name;
    assert (List.length sorts > 0);
    List.iter sorts ~f:(app_space fmt);
    Format.fprintf fmt ")\n"

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


