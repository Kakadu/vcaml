type program
type loc
type loc_set
type level_t = int
type formula
type formula_set
type pobs_set
type store_t
type state_set
type pob_state_set

module PobMap = struct type _ t end
module LocMap = struct type _ t end
module LocLevelMap = struct type _ t end
type pob = { pob_loc: loc; phi: formula; pob_lvl: level_t }
type state =
{ st_loc : loc;
  pc : formula ;
  store: store_t;
  loc0: formula;
  st_lvl: level_t;
  pobs : pobs_set;
}

type globals =
{ mutable curLvl: level_t
; mutable main_pobs: pobs_set
; mutable pobs : pobs_set
; mutable qf: state_set
; mutable qb: pob_state_set
; mutable witnesses: state_set PobMap.t
; mutable blocked_locs: loc_set PobMap.t
; mutable pobs_locs: loc_set
; mutable t : state_set LocMap.t
; mutable l : formula_set LocLevelMap.t
; mutable child: pobs_set PobMap.t
}

module type IFACE = sig
  val propDirSymExec : loc_set -> program -> unit
  val forward : state -> unit
  val backward : pob -> state -> program -> level_t
  val answerYes: pob -> unit
  val answerNo : pob -> unit

  val canReach: loc -> loc -> loc_set -> bool

  val checkInductive : level_t -> unit

  val addWitness : state -> pob -> unit

  val blockWitness: state -> pob -> unit

  val overApxm: loc -> lvl:level_t -> cur_lvl:level_t -> formula

  val encode: state -> formula

  val wlp : state -> formula -> formula
end
