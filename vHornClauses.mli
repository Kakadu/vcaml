module type HornAPI = sig
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

module V1: HornAPI
module V2: HornAPI

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
    val app : expr -> expr list -> expr
    val find : heap_index -> expr
    val switch_ident : ident -> (ident * expr) list -> expr
    val ite : expr -> expr -> expr -> expr

    val unreachable: expr
    val todo: expr
  end
  module SI : sig
    val find : heap_index -> (string -> string -> expr) -> si
    val assert_: ?name:string -> string list -> expr -> si
  end

  val program : si list -> program
  val join_programs : program list -> program
  val pp_program : Format.formatter -> program -> unit
end

module ML : ML_API
