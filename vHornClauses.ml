open Base

module type HornAPI =  sig
  type clause
  type formula  = Format.formatter -> unit
  type term = Format.formatter -> unit
  type sort = Format.formatter -> unit

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
    val neg : term -> formula
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

(*
(* ************************************************************************** *)
(* when phormulas bubble up from terms *)
module V2 = struct
  type formula = (Format.formatter -> unit) list
  type term_kind = Plain | Var
  type term = (Format.formatter -> unit) * term_kind * formula
  type sort = Format.formatter -> unit

  (* TODO: can Horn Clause has empty list of premises? *)
  type clause = formula option * formula list

  let clause ?head fs = (head, fs)
  (* TODO: what happend when head is a list of formulas *)

  module T = struct
    let nof x = (x, Plain, [])

    let int  n = nof (fun fmt -> Format.fprintf fmt "%d" n)
    let bool b = nof (fun fmt -> Format.fprintf fmt "%b" b)
    let var  s = nof (fun fmt -> Format.fprintf fmt "%s" s
    let call_uf s xs =
      let ans fmt =
        Format.fprintf fmt "@[(%s " s;
        List.iter xs ~f:(fun f  -> f fmt; Format.fprintf fmt "@ ");
        Format.fprintf fmt ")@]@ "
      in
      (ans, Var, [])
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

end
*)
