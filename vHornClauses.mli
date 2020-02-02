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

module V1: HornAPI
