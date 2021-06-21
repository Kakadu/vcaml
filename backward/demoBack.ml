open Base
open Ppx_compare_lib.Builtin

let failwiths fmt = Format.kasprintf failwith fmt
let log fmt = Format.kasprintf (Format.printf "%s") fmt

module Loc = struct
  type t = int [@@deriving compare, sexp_of]

  module X = struct
    type nonrec t = t

    let compare = compare
  end

  module Set = struct
    include Stdlib.Set.Make (X)

    let pp ppf set =
      Format.fprintf ppf "{loc set| " ;
      iter (Format.fprintf ppf "%d, ") set ;
      Format.fprintf ppf "|}"
  end

  module Map = struct
    include Stdlib.Map.Make (X)

    let find_exn k m = find k m
    let replace k v s = add k v s
  end

  let eq : t -> t -> bool = Int.equal
  let replace k v m = Map.add k v m
end

type loc_set = Loc.Set.t
type inf_level
type ground_level

type 'a level_t =
  | LvlInt : int -> ground_level level_t
  | LvlInf : inf_level level_t
[@@deriving sexp_of]

let int_of_level : ground_level level_t -> int = function LvlInt n -> n

let compare_level_t :
      'a 'b. ('a -> 'b -> int) -> 'a level_t -> 'b level_t -> int =
  fun (type a b) _ (a : a level_t) (b : b level_t) : int ->
   match (a, b) with
   | LvlInf, LvlInf -> 0
   | LvlInt _, LvlInf -> 1
   | LvlInf, LvlInt _ -> -1
   | LvlInt l, LvlInt r -> compare_int l r

let my_compare_level a b = compare_level_t (fun _ _ -> assert false) a b

let pp_level_t (type a) : Format.formatter -> a level_t -> unit =
 fun ppf -> function
  | LvlInt n -> Format.fprintf ppf "%d" n
  | LvlInf -> Format.fprintf ppf "∞"

module Formula = struct
  type t =
    | True
    | False
    | Conj of t * t
    | Disj of t * t
    (* terms *)
    | LT of t * t
    | EQ of t * t
    | LE of t * t
    | Symb of string
    (* | ConcVar of string *)
    | Add of t * t
    | Int of int
  [@@deriving compare, show, sexp_of]

  let pp ppf =
    let rec helper = function
      | True -> Format.fprintf ppf "⊤"
      | False -> Format.fprintf ppf "⊥"
      | LT (l, r) -> Format.fprintf ppf "(%a %s %a)" pp l "<" pp r
      | s -> pp ppf s in
    helper

  let symb s = Symb s
  let add l r = Add (l, r)
  let ( + ) = add
  let int n = Int n
  let true_ = True
  let false_ = False
  let le a b = LE (a, b)
  let ( <= ) = le
  let eq a b = EQ (a, b)
  let ( = ) = eq
  let conj a b = Conj (a, b)
  let ( && ) = conj
  let var s = symb s

  module Set = Stdlib.Set.Make (struct
    type nonrec t = t

    let compare = compare
  end)
end

let z3_of_formula f =
  let ctx = Z3.mk_context [] in
  let open FancyZ3 in
  let (module T), (module F) = FancyZ3.to_z3 ctx in
  let rec onf = function
    | Formula.True -> F.true_
    | False -> F.not F.true_
    | Conj (l, r) -> F.conj (onf l) (onf r)
    | Disj (l, r) -> F.disj (onf l) (onf r)
    | EQ (l, r) -> F.eq (onf l) (onf r)
    | LT (l, r) -> F.lt (onf l) (onf r)
    | LE (l, r) -> F.le (onf l) (onf r)
    | Symb s -> T.var s
    | Int n -> T.const_int n
    | Add (l, r) -> T.add (onf l) (onf r) in
  (onf f, ctx)

module Store = struct
  module StringMap = Stdlib.Map.Make (String)

  type t = Formula.t StringMap.t [@@deriving compare]

  let add = StringMap.add
  let empty = StringMap.empty
  let find_exn = StringMap.find
  let replace = StringMap.add
end

module POB = struct
  (* FIXME: GADT indexes fuck up generic programming
     TODO: maybe annotate parameters-as-indexes and generate more smart comparison functions ? *)
  type 'a t = {pob_loc: Loc.t; phi: Formula.t; pob_lvl: 'a level_t}
  [@@deriving compare, sexp_of]

  let my_compare : 'a 'b. 'a t -> 'b t -> int =
   fun {pob_loc; phi; pob_lvl} {pob_loc= pob_loc2; phi= xi; pob_lvl= pob_lvl2} ->
    match Loc.compare pob_loc pob_loc2 with
    | 0 -> (
      match Formula.compare phi xi with
      | 0 -> compare_level_t (fun _ _ -> assert false) pob_lvl pob_lvl2
      | n -> n )
    | n -> n

  let loc {pob_loc} = pob_loc
  let pob_lvl {pob_lvl} = pob_lvl
  let level : ground_level t -> int = function {pob_lvl= LvlInt n} -> n
  let formula {phi} = phi
  let create pob_loc phi pob_lvl = {pob_loc; phi; pob_lvl}

  let pp ppf {pob_loc; phi; pob_lvl} =
    Format.fprintf ppf "{POB| loc=%d; φ=%a; lvl=%a|}" pob_loc Formula.pp phi
      pp_level_t pob_lvl

  type 'a pob = 'a t

  module X = struct
    type gt = POB : 'a t -> gt [@@deriving sexp_of]
    type t = gt

    include Comparator.Make (struct
      type t = gt

      let compare a b = match (a, b) with POB l, POB r -> my_compare l r
      let sexp_of_t = sexp_of_gt
    end)
  end

  module Set = struct
    type key = X.gt
    type 'a pob = 'a t
    type t = (key, X.comparator_witness) Set.t

    let cmp :
        (module Comparator.S
           with type comparator_witness = X.comparator_witness
            and type t = X.t ) =
      (module X)

    let size = Set.length
    let empty : t = Set.empty cmp
    let is_empty = Set.is_empty
    let add_exn : 'a pob -> t -> t = fun k s -> Set.add s (X.POB k)
    let remove : 'a pob -> t -> t = fun k s -> Set.remove s (X.POB k)

    let compare : t -> t -> int =
     (* TODO: Ask why I should write this shit *)
     fun l r -> Base.Set.compare_m__t (module struct end) l r

    let iter : f:(key -> unit) -> t -> unit =
     fun ~f set -> Base.Set.iter set ~f:(fun k -> f k)
  end

  module Map = struct
    type 'a t = (X.t, 'a, X.comparator_witness) Map.t

    let cmp = Set.cmp
    let empty : _ t = Map.empty cmp

    let compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int =
     (* TODO: Ask why I should write this shit *)
     fun onval l r -> Base.Map.compare_m__t (module struct end) onval l r

    let find_exn : 'a pob -> 'b t -> 'b =
     fun k m -> Base.Map.find_exn m (X.POB k)

    let remove_all ~key t = Base.Map.remove t (X.POB key)
    let remove ~key t data = Base.Map.remove t (X.POB key)
    let update = Base.Map.update
    (* let replace key date m =
       match Base.Map.add ~key ~data m with
       | `Duplicate -> find_exn key m *)
  end
end

(** Symbolic state *)
module State = struct
  (* TODO: say in the interface that it is private *)
  type t =
    { idx: int
    ; loc: Loc.t
    ; pc: Formula.t
    ; store: Store.t
    ; loc0: Loc.t
    ; lvl: ground_level level_t
    ; mutable pobs: POB.Set.t }

  let my_compare {idx} {idx= idx2} = compare_int idx idx2
  let index {idx} = idx
  let loc {loc} = loc
  let pc {pc} = pc
  let loc0 {loc0} = loc0
  let store {store} = store
  let pobs {pobs} = pobs
  let level : t -> int = function {lvl= LvlInt n} -> n
  let last = ref 0
  let pp ppf {idx; loc} = Format.fprintf ppf "{state| idx=%d; loc=%d |}" idx loc

  type state = t

  let create ~loc ~loc0 store pc lvl pobs =
    incr last ;
    {idx= !last; loc; loc0; pc; store; lvl; pobs}

  let add_pob st pob = st.pobs <- POB.Set.add_exn pob st.pobs
  let remove_pob st pob = st.pobs <- POB.Set.remove pob st.pobs

  module X = struct
    type nonrec t = t

    include Comparator.Make (struct
      type nonrec t = t

      let compare = my_compare
      let sexp_of_t = function _ -> assert false
    end)
  end

  module Set = struct
    type t = (X.t, X.comparator_witness) Set.t

    let cmp :
        (module Comparator.S
           with type comparator_witness = X.comparator_witness
            and type t = X.t ) =
      (module X)

    let empty : t = Set.empty cmp
    let is_empty = Set.is_empty
    let singleton x : t = Set.singleton cmp x

    let compare : t -> t -> int =
     (* TODO: Ask why I should write this shit *)
     fun l r -> Base.Set.compare_m__t (module struct end) l r

    let iter : t -> f:(_ -> unit) -> _ = Base.Set.iter
    let fold : t -> _ = Base.Set.fold
    let add k s : t = Base.Set.add s k
    let remove k set = Base.Set.remove set k

    let remove_min set : state * t =
      let h = Base.Set.min_elt_exn set in
      let set0 = Base.Set.remove set h in
      (h, set0)
  end
end

module PobStateSet = struct
  module X = struct
    type t = P : 'a POB.t * State.t -> t

    include Comparator.Make (struct
      type nonrec t = t

      let compare (P (a, c)) (P (b, d)) =
        match POB.my_compare a b with 0 -> State.my_compare c d | n -> n

      let sexp_of_t = function _ -> assert false
    end)
  end

  type 'a key = 'a POB.t * State.t
  type t = (X.t, X.comparator_witness) Set.t

  let cmp :
      (module Comparator.S
         with type comparator_witness = X.comparator_witness
          and type t = X.t ) =
    (module X)

  let empty : t = Set.empty cmp
  let is_empty = Set.is_empty

  let compare : t -> t -> int =
   (* TODO: Ask why I should write this shit *)
   fun l r -> Base.Set.compare_m__t (module struct end) l r

  let remove : _ key -> t -> t = fun (p, st) s -> Set.remove s (X.P (p, st))
  let add : _ key -> t -> t = fun (p, st) s -> Set.add s (X.P (p, st))

  let remove_min (set : t) : _ * t =
    let (X.P (_, _) as k) = Base.Set.min_elt_exn set in
    let set0 = Base.Set.remove set k in
    (k, set0)
end

module Program = struct
  type t = {ep: Loc.t}

  let create ep = {ep}
  let ep {ep} = ep
end

type program = Program.t
type state = State.t
type 'a pob = 'a POB.t
type state_set = State.Set.t
type pob_state_set = PobStateSet.t
type pobs_set = POB.Set.t

module LocLevelMap = struct
  module Key = struct
    type t = X : Loc.t * 'a level_t -> t

    let compare (X (a, c)) (X (b, d)) =
      match Loc.compare a b with 0 -> my_compare_level c d | n -> n
  end

  include Stdlib.Map.Make (Key)

  let add : Loc.t * _ level_t -> 'v -> 'v t -> 'v t =
   fun (l, l2) v m -> add (Key.X (l, l2)) v m

  let add_ground_lvl (loc, lvln) = add (loc, LvlInt lvln)
  let find_exn ~key:(loc, lvl) m = find (Key.X (loc, lvl)) m
end

module Witnesses = struct
  (* include (POB.Map: (module type of POB.Map) with type 'a t := (POB.X.gt, int, POB.X.comparator_witness) Base.Map.t) *)
  include POB.Map

  type ws = State.Set.t t

  let add_multi ~key ~data m : ws =
    Base.Map.update m (POB.X.POB key) ~f:(function
      | None -> State.Set.singleton data
      | Some s -> State.Set.add data s )

  let iter_key ~key m ~f =
    State.Set.iter (Base.Map.find_exn m (POB.X.POB key)) ~f

  let find_exn ~key m = POB.Map.find_exn key m
end

type strategy_rez =
  | SRStart : Loc.t -> strategy_rez
  | SRGoFront : State.t -> strategy_rez
  | SRGoBack : ground_level POB.t * State.t -> strategy_rez

type globals =
  { mutable curLvl: ground_level level_t
  ; mutable main_pobs: pobs_set
  ; mutable pobs: pobs_set
  ; mutable qf: state_set
  ; mutable qb: pob_state_set
  ; mutable witnesses: state_set POB.Map.t
  ; mutable blocked_locs: loc_set POB.Map.t
  ; mutable pobs_locs: loc_set
  ; mutable t: state_set Loc.Map.t
  ; mutable l: Formula.Set.t LocLevelMap.t
  ; mutable child: pobs_set POB.Map.t
  ; strategy: strategy_t }

and strategy_t =
  { chooseAction:
      globals -> program -> (* state_set -> pob_state_set -> *) strategy_rez }

module type IFACE = sig
  type g

  val propDirSymExec : unit -> unit
  val print_results : unit -> unit
  val forward : state -> unit

  val backward :
    ground_level pob -> state -> program -> ground_level level_t -> unit

  val checkInductive : 'a level_t -> unit
  val addWitness : state -> ground_level pob -> unit
  val blockWitness : state -> ground_level pob -> unit

  (* TODO: replace ints by ground_levels *)
  val overApxm : Loc.t -> lvl:int -> cur_lvl:ground_level level_t -> Formula.t
  val encode : state -> Formula.t
  val wlp : state -> Formula.t -> Formula.t

  (** External functions *)

  val isSat : Formula.t -> bool
  val answerYes : 'a pob -> unit
  val answerNo : 'a pob -> unit
  val nextLevel : g -> unit
  val canReach : Loc.t -> dst:Loc.t -> loc_set -> bool
  val executeInstruction : state -> Loc.t -> state_set
  val mkPrime : Formula.t -> Formula.t
end

module G = struct
  let add_child g ch ~parent = assert false
  let add_to_qb g (p, st) = g.qb <- PobStateSet.add (p, st) g.qb
  let add_to_qf g s = g.qf <- State.Set.add s g.qf
  let remove_from_qf g s = g.qf <- State.Set.remove s g.qf
  let add_to_l g loc lvl new_val = g.l <- LocLevelMap.add (loc, lvl) new_val g.l

  let add_to_t g loc (st : state) =
    let next_set =
      try
        let old = Loc.Map.find loc g.t in
        State.Set.add st old
      with Not_found -> State.Set.singleton st in
    g.t <- Loc.Map.replace loc next_set g.t

  let blocked_locs g p = POB.Map.find_exn p g.blocked_locs
  let t p' = assert false

  let add_witness g ~(key : _ POB.t) st =
    g.witnesses <- Witnesses.add_multi ~key ~data:st g.witnesses

  let remove_witness g ~key w =
    g.witnesses <- Witnesses.remove ~key g.witnesses w

  let block_loc g p loc =
    g.blocked_locs <-
      POB.Map.update g.blocked_locs (POB.X.POB p) ~f:(function
        | None -> Loc.Set.singleton loc
        | Some ss -> Loc.Set.add loc ss )

  let add_pob g p = g.pobs <- POB.Set.add_exn p g.pobs
  let choose_action g prog = g.strategy.chooseAction g prog
end

module Hardcoded = struct
  (*
    1 Function F()
    2   x := 1; y := 1;
    3   while nondet() do
    4     x := x + y;
    5     y := x;
    6   if x ≤ 0 then
    7     fail();

           ---> 7
           |
    2 ---> 3 <---
           |    |
           ---> 5

  *)
  let canReach src ~dst loc_set =
    match (src, dst) with
    | 2, 7 -> not (Loc.Set.mem 3 loc_set)
    | _ ->
        failwiths "canReach not implemented: %d -> %d avoiding %a " src dst
          Loc.Set.pp loc_set

  let execute_instruction st loc : state_set =
    let module M = struct
      type instr = Assn of string * expr

      and expr = EConst of int | ESym of string | EAdd of expr * expr
    end in
    let open M in
    (* fat dot *)
    let rec app_eff (eff : Store.t) = function
      | M.EConst n -> Formula.int n
      | M.ESym s -> (
        match Store.find_exn s eff with
        | exception Not_found -> Formula.symb s
        | t -> t )
      | M.EAdd (l, r) -> Formula.add (app_eff eff l) (app_eff eff r) in
    let rec fat_dot eff (M.Assn (dest, e)) : Store.t =
      match e with
      | M.EConst n -> Store.(eff |> add dest (Formula.int n))
      | M.ESym _ | M.EAdd (_, _) -> Store.(eff |> replace dest (app_eff eff e))
    in
    let next_level = LvlInt (State.level st + 1) in
    let eff0 = State.store st in
    match loc with
    | 2 ->
        State.Set.singleton
        @@ State.create ~loc0:0 ~loc:3
             (fat_dot
                (fat_dot eff0 M.(Assn ("x", EConst 1)))
                M.(Assn ("y", EConst 1)) )
             Formula.true_ next_level POB.Set.empty
    | 3 ->
        let ans5 =
          State.create ~loc0:0 ~loc:5 eff0 Formula.true_ next_level
            POB.Set.empty in
        let ans7 =
          State.create ~loc0:0 ~loc:7 eff0
            Formula.(symb "x" <= int 0)
            next_level POB.Set.empty in
        State.Set.(empty |> add ans5 |> add ans7)
    | 5 ->
        State.Set.singleton
        @@ State.create ~loc0:0 ~loc:3
             (fat_dot
                (fat_dot eff0 M.(Assn ("x", EAdd (ESym "x", ESym "y"))))
                M.(Assn ("y", ESym "x")) )
             Formula.true_ next_level POB.Set.empty
    | 7 -> State.Set.empty
    | _ -> failwith "unreachable"

  let pM : _ POB.t = POB.create 7 True LvlInf

  let s1 : state =
    State.create ~loc0:2 ~loc:3
      Store.(empty |> add "x" (Formula.int 1) |> add "y" (Formula.int 1))
      Formula.True (LvlInt 0)
      POB.Set.(add_exn pM empty)

  let s2 : state =
    State.create ~loc0:3 ~loc:5
      Store.(
        empty
        |> add "x" Formula.(add (symb "x") (symb "y"))
        |> add "y" (Formula.symb "y"))
      Formula.True (LvlInt 0)
      POB.Set.(add_exn pM empty)

  let s3 : state =
    State.create ~loc0:5 ~loc:3
      Store.(empty |> add "x" Formula.(symb "x") |> add "y" (Formula.symb "x"))
      Formula.True (LvlInt 1)
      POB.Set.(add_exn pM empty)

  let s4 : state =
    State.create ~loc0:3 ~loc:7
      Store.(empty |> add "x" Formula.(symb "x") |> add "y" (Formula.symb "x"))
      Formula.(le (symb "x") (int 0))
      (LvlInt 0)
      POB.Set.(add_exn pM empty)

  let strat1 : strategy_t =
    let chooseAction g prog =
      if not (PobStateSet.is_empty g.qb) then (
        let PobStateSet.X.P (pob, st), qb0 = PobStateSet.remove_min g.qb in
        g.qb <- qb0 ;
        match pob.pob_lvl with
        | LvlInt _ -> SRGoBack (pob, st)
        | _ -> assert false )
      else if not (State.Set.is_empty g.qf) then
        let st, set0 = State.Set.remove_min g.qf in
        let () = g.qf <- set0 in
        SRGoFront st
      else SRStart (Program.ep prog) in
    {chooseAction}

  let init g =
    g.main_pobs <-
      POB.Set.add_exn (POB.create 7 Formula.True (LvlInt 0)) g.main_pobs ;
    let p0 = POB.create 7 Formula.True (LvlInt 0) in
    G.add_witness g ~key:p0 s4 ;
    G.add_witness g ~key:p0 s4 ;
    G.block_loc g p0 5 ;
    ()

  let program = Program.create 2
end

module type LEMMAS = sig
  type t

  val add_exn : Loc.t -> _ level_t -> Formula.t -> t -> t
end

(* let init_lemmas prog_locs =
  let module M = struct end in
  (module M : LEMMAS) *)

module Lemmas = struct
  include LocLevelMap

  type nonrec t = Formula.Set.t t

  let find : 'a. Loc.t -> 'a level_t -> t -> _ =
    fun (type a) loc (level : a level_t) (map : t) ->
     try LocLevelMap.find_exn ~key:(loc, level) map
     with Not_found -> (
       (* FIXME: we oversimplified the stuff. In realitry locations should always be program locations *)
       match level with
       | LvlInf -> raise Not_found
       | LvlInt level ->
           Formula.Set.singleton
             (if level < 0 then Formula.false_ else Formula.true_) )
end

let make_algo query_locs program =
  let module Impl : IFACE = struct
    type g = globals

    let init_globals () =
      let g =
        { curLvl= LvlInt 0
        ; main_pobs= POB.Set.empty
        ; pobs= POB.Set.empty
        ; qf= State.Set.empty
        ; qb= PobStateSet.empty
        ; witnesses= POB.Map.empty
        ; blocked_locs= POB.Map.empty
        ; pobs_locs= Loc.Set.empty
        ; t= Loc.Map.empty
        ; l= LocLevelMap.empty
        ; child= POB.Map.empty
        ; strategy= Hardcoded.strat1 } in
      query_locs
      |> Loc.Set.iter (fun loc ->
             g.main_pobs <-
               POB.Set.add_exn (POB.create loc Formula.True LvlInf) g.main_pobs ;
             g.pobs_locs <- Loc.Set.add loc g.pobs_locs ) ;
      g

    let g : globals = init_globals ()
    let canReach src ~dst x = Hardcoded.canReach src ~dst x

    let addWitness st (p : ground_level POB.t) =
      if
        State.level st <= POB.level p
        && canReach (State.loc st) ~dst:(POB.loc p) (G.blocked_locs g p)
      then
        let () = G.add_witness g ~key:p st in
        State.add_pob st p

    let rec blockWitness s' p' =
      log "blockWitness: state = %a, p=%a\n%!" State.pp s' POB.pp p' ;
      With_return.with_return (fun r ->
          State.remove_pob s' p' ;
          G.remove_witness g ~key:p' s' ;
          Witnesses.iter_key g.witnesses ~key:p' ~f:(fun s ->
              if State.loc0 s = State.loc0 s' then r.return () ) ;
          G.block_loc g p' (State.loc0 s') ;
          State.Set.iter (Witnesses.find_exn g.witnesses ~key:p') ~f:(fun s ->
              if
                not
                  (canReach (State.loc s) ~dst:(POB.loc p')
                     (G.blocked_locs g p') )
              then blockWitness s p' ) )

    let wlp _ _ = assert false

    let isSat, isUnsat =
      let helper onSat onUnsat f =
        let z3f, ctx = z3_of_formula f in
        let solver = Z3.Solver.mk_simple_solver ctx in
        match Z3.Solver.check solver [z3f] with
        | Z3.Solver.UNKNOWN -> failwith "should not happen"
        | Z3.Solver.UNSATISFIABLE -> onUnsat ()
        | Z3.Solver.SATISFIABLE -> onSat () in
      ( helper (fun _ -> true) (fun _ -> false)
      , helper (fun _ -> false) (fun _ -> true) )

    let answerYes _ = assert false
    let answerNo _ = assert false

    let overApxm loc ~lvl ~cur_lvl =
      let apxm = ref Formula.False in
      let () =
        for lvl' = lvl to int_of_level cur_lvl do
          apxm :=
            Formula.Set.fold Formula.conj
              (LocLevelMap.find_exn ~key:(loc, LvlInt lvl') g.l)
              !apxm
        done in
      !apxm

    let nextLevel g = g.curLvl <- (match g.curLvl with LvlInt n -> LvlInt n)
    let executeInstruction = Hardcoded.execute_instruction
    let mkPrime _ = assert false
    let checkInductive _ = assert false
    let generalize _ _ = assert false

    let encode : state -> Formula.t =
      (* Тут можно генерировать формулки для Z3, так как по ним мэтчиться не придется
         Но там надо будет вместо штрихов придумывать новые имена
      *)
      let warned = ref false in
      fun st ->
        let () =
          if not !warned then (
            warned := true ;
            Format.eprintf "Hardcoded `encode` implementation\n%!" ) in
        let open Formula in
        let x = symb "x" in
        let x' = x in
        let y = symb "y" in
        let y' = y in
        let _1 = int 1 in
        let _0 = int 0 in
        match State.index st with
        | 1 -> x' = _1 && y' = _1
        | 2 -> x' = x + y && y' = y
        | 3 -> x' = x && y' = x
        | 4 -> x' <= _0 && x' = x && y' = y
        | _ -> failwith "Should not happen in demo example"

    let start loc =
      let () = log "Action start: %s %d\n%!" __FILE__ __LINE__ in
      let s =
        State.create ~loc ~loc0:loc Store.empty Formula.True (LvlInt 0)
          POB.Set.empty in
      g.qf <- State.Set.add s g.qf ;
      G.add_to_t g loc s ;
      POB.Set.iter g.pobs ~f:(fun (POB.X.POB p) ->
          match POB.pob_lvl p with
          | LvlInf -> assert false
          | LvlInt n -> addWitness s p )

    let backward p' s' prog cur_lvl =
      log "backward: pob = %a\n%!" POB.pp p' ;
      g.qb <- PobStateSet.(remove (p', s') g.qb) ;
      assert (Loc.eq (POB.loc p') (State.loc s')) ;
      let lvl = POB.level p' - State.level s' in
      let () = assert (lvl >= 0) in
      let psi =
        Formula.conj
          (wlp s' (POB.formula p'))
          (overApxm (State.loc0 s') ~lvl ~cur_lvl) in
      ( if isSat psi then (
        if POB.loc p' = Program.ep prog then answerYes p'
        else
          let p = POB.create (State.loc0 s') psi (LvlInt lvl) in
          let () = g.pobs <- POB.Set.add_exn p g.pobs in
          let () = G.add_child g ~parent:p' p in
          State.Set.iter (POB.Map.find_exn p' g.witnesses) ~f:(fun s ->
              addWitness s p ) ;
          State.Set.iter
            (Loc.Map.find_exn (POB.loc p) g.t)
            ~f:(fun s -> G.add_to_qb g (p, s)) )
      else
        let () = blockWitness s' p' in
        if canReach (Program.ep prog) ~dst:(POB.loc p') (G.blocked_locs g p')
        then () (*return *)
        else
          let () = answerNo p' in
          let apxm =
            State.Set.fold
              (G.t (POB.loc p'))
              ~init:Formula.False
              ~f:(fun acc s ->
                if Loc.Set.mem (State.loc0 s) (G.blocked_locs g p') then
                  Formula.(
                    acc
                    && overApxm (State.loc0 s)
                         ~lvl:(POB.level p' - State.level s)
                         ~cur_lvl
                    && encode s)
                else acc ) in
          let () =
            G.add_to_l g (POB.loc p')
              (LvlInt (POB.level p'))
              (generalize apxm (POB.formula p')) in
          checkInductive cur_lvl ) ;
      ()

    let forward s =
      log "forward: pob = %a\n%!" State.pp s ;
      G.remove_from_qf g s ;
      State.Set.iter
        (executeInstruction s (State.loc s))
        ~f:(fun s' ->
          assert (isSat (State.pc s')) ;
          G.add_to_qf g s' ;
          if Loc.Set.mem (State.loc s') g.pobs_locs then
            G.add_to_t g (State.loc s') s' ;
          POB.Set.iter (State.pobs s) ~f:(fun (POB.X.POB p) ->
              match POB.pob_lvl p with
              | LvlInf -> assert false
              | LvlInt lvl ->
                  addWitness s' p ;
                  if POB.loc p = State.loc s' then G.add_to_qb g (p, s') ) ) ;
      POB.Set.iter (State.pobs s) ~f:(fun (POB.X.POB p) ->
          if POB.loc p <> State.loc s then blockWitness s p )

    let print_results () = failwith "TODO: report error"

    let propDirSymExec () =
      (* let g = init_globals () in *)
      log "After initialization: main_pobs.count = %d\n%!"
        (POB.Set.size g.main_pobs) ;
      Hardcoded.init g ;
      Format.printf "%s %d\n%!" __FILE__ __LINE__ ;
      let rec loop () =
        if POB.Set.is_empty g.main_pobs then ()
        else
          let () =
            POB.Set.iter g.main_pobs ~f:(fun (POB.X.POB p) ->
                G.add_pob g POB.(create (POB.loc p) Formula.True g.curLvl) )
          in
          let rec loop_pobs () =
            let () = Format.printf "loop_pobs: %s %d\n%!" __FILE__ __LINE__ in
            let () =
              match G.choose_action g program with
              | SRStart loc -> start loc
              | SRGoFront st -> forward st
              | SRGoBack (p', st') -> backward p' st' program g.curLvl in
            loop_pobs () in
          let () = loop_pobs () in
          let () = Format.printf "%s %d\n%!" __FILE__ __LINE__ in
          (* g.curLvl <- nextLevel g.curLvl; *)
          nextLevel g in
      let () = loop () in
      print_results ()
  end in
  (module Impl : IFACE)

let () =
  let (module M : IFACE) = make_algo (Loc.Set.singleton 7) Hardcoded.program in
  M.propDirSymExec ()
