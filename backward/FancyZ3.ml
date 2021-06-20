(* https://z3prover.github.io/api/html/ml/Z3.html
*)

module type FINAL_TAGLESS_BASE = sig
  type t
  type rez

  val finish : t -> rez
end

module type TERM = sig
  include FINAL_TAGLESS_BASE

  val var : string -> t

  (* val const_s : string -> t *)
  val const_int : int -> t

  (* val land_ : t -> t -> t *)
  (* val lor_ : t -> t -> t *)
  val add : t -> t -> t
  (* val sub : t -> t -> t
     val mul : t -> t -> t
     val shl : t -> t -> t
     val lshr : t -> t -> t *)
end

module type RICH_TERM = sig
  include TERM

  val ( + ) : t -> t -> t

  (* val ( * ) : t -> t -> t *)
  (* val shl1 : t -> t *)
  (* val lshr1 : t -> t *)

  (* TODO: power *)
  val i : int -> t
end

module EnrichTerm (T : TERM) : RICH_TERM with type t = T.t = struct
  include T

  let ( + ) = add

  (* let ( * ) = mul *)
  let i n = const_int n
  (* let shl1 x = shl x (i 1) *)
  (* let lshr1 x = lshr x (i 1) *)
end

module type FORMULA = sig
  include FINAL_TAGLESS_BASE

  type term

  val true_ : t
  val eq : term -> term -> t
  val lt : term -> term -> t
  val le : term -> term -> t
  val conj : t -> t -> t
  val disj : t -> t -> t
  val not : t -> t
  val iff : t -> t -> t
  val forall : string -> t -> t
  val exists : string -> t -> t
end

module type RICH_FORMULA = sig
  include FORMULA

  val ( == ) : term -> term -> t
  val ( < ) : term -> term -> t
  val ( > ) : term -> term -> t
  val ( <= ) : term -> term -> t
  val ( && ) : t -> t -> t
  val ( || ) : t -> t -> t
  val ( <=> ) : t -> t -> t
end

module EnrichFormula (F : FORMULA) :
  RICH_FORMULA with type t = F.t and type term = F.term = struct
  include F

  let ( == ) = eq
  let ( < ) = lt
  let ( > ) a b = lt b a
  let ( <= ) = le
  let ( <=> ) = iff
  let ( || ) = disj
  let ( && ) = conj
end

type z3_expr = Z3.Expr.expr

let bv_size = 32

module type FORMULA_Z3 =
  FORMULA with type t = z3_expr and type term = z3_expr and type rez = z3_expr

module type TERM_Z3 = TERM with type t = z3_expr

let z3_of_term ctx =
  let module T = struct
    open Z3

    type t = Z3.Expr.expr
    type rez = t

    let finish = Fun.id
    let var s = BitVector.mk_const ctx (Symbol.mk_string ctx s) bv_size
    let const_s s = Expr.mk_numeral_string ctx s (BitVector.mk_sort ctx bv_size)

    let const_int n =
      (* creates `|9|`, etc. WHY??? *)
      (* BitVector.mk_const_s ctx (string_of_int n) bv_size *)
      (* ugly but works *)
      const_s (string_of_int n)

    let land_ = BitVector.mk_and ctx
    let lor_ = BitVector.mk_or ctx
    let shl = BitVector.mk_shl ctx
    let lshr = BitVector.mk_lshr ctx
    let add = BitVector.mk_add ctx
    let sub = BitVector.mk_sub ctx
    let mul = BitVector.mk_mul ctx
  end in
  (module T : TERM with type t = T.t and type rez = T.t)

let z3_of_formula ctx =
  let module P = struct
    open Z3

    type t = z3_expr
    type rez = t

    let finish = Fun.id

    type term = z3_expr

    let true_ = Boolean.mk_true ctx
    let iff a b = Boolean.mk_iff ctx a b
    let not = Boolean.mk_not ctx
    let conj a b = Boolean.mk_and ctx [a; b]
    let disj a b = Boolean.mk_or ctx [a; b]
    let eq = Boolean.mk_eq ctx
    let le = BitVector.mk_ule ctx
    let lt = BitVector.mk_ult ctx

    let forall name f =
      let x = BitVector.mk_const ctx (Symbol.mk_string ctx name) bv_size in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [x] f None [] [] None None)

    let exists name f =
      let x = BitVector.mk_const ctx (Symbol.mk_string ctx name) bv_size in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_exists_const ctx [x] f None [] [] None None)
  end in
  (module P : FORMULA
    with type t = z3_expr
     and type term = z3_expr
     and type rez = z3_expr )

let to_z3 :
       Z3.context
    -> (module TERM with type t = z3_expr and type rez = z3_expr)
       * (module FORMULA
            with type t = z3_expr
             and type term = z3_expr
             and type rez = z3_expr ) =
 fun ctx -> (z3_of_term ctx, z3_of_formula ctx)
