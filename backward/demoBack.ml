open Base
open Ppx_compare_lib.Builtin

let failwiths fmt = Format.kasprintf failwith fmt

module Loc = struct
  type t = int [@@deriving compare]

  module X = struct
    type nonrec t = t

    let compare = compare
  end

  module Set = Stdlib.Set.Make (X)

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

module Term = struct
  type t = Symb of string | ConcVar of string | Add of t * t | Int of int
  [@@deriving compare]

  let symb s = Symb s

  (* let var s = ConcVar s *)
  let add l r = Add (l, r)
  let ( + ) = add
  let int n = Int n
end

module Formula = struct
  type t =
    | True
    | False
    | Conj of t * t
    | Disj of t * t
    | LT of Term.t * Term.t
    | EQ of Term.t * Term.t
    | LE of Term.t * Term.t
    | Term of Term.t
  [@@deriving compare]

  let term t = Term t
  let le a b = LE (a, b)
  let ( <= ) = le
  let eq a b = EQ (a, b)
  let ( = ) = eq
  let conj a b = Conj (a, b)
  let ( && ) = conj

  module Set = Stdlib.Set.Make (struct
    type nonrec t = t

    let compare = compare
  end)
end

let z3_of_formula f =
  let ctx = Z3.mk_context [] in
  let open FancyZ3 in
  let (module T), (module F) = FancyZ3.to_z3 ctx in
  let rec ont = function
    | Term.Symb s -> T.var s
    | Int n -> T.const_int n
    | Add (l, r) -> T.add (ont l) (ont r)
    | _ -> failwith "TODO: remove concrete vars"
  and onf = function
    | Formula.True -> F.true_
    | False -> F.not F.true_
    | Conj (l, r) -> F.conj (onf l) (onf r)
    | Disj (l, r) -> F.disj (onf l) (onf r)
    | EQ (l, r) -> F.eq (ont l) (ont r)
    | LT (l, r) -> F.lt (ont l) (ont r)
    | LE (l, r) -> F.le (ont l) (ont r)
    | Term t -> ont t in
  (onf f, ctx)

module Store = struct
  module StringMap = Stdlib.Map.Make (String)

  type t = Formula.t StringMap.t
  (* TODO: formula or term? *) [@@deriving compare]

  let add = StringMap.add
  let empty = StringMap.empty
end

module POB = struct
  (* FIXME: GADT indexes fuck up generic programming
     TODO: maybe annotate parameters-as-indexes and generate more smart comparison functions ? *)
  type 'a t = {pob_loc: Loc.t; phi: Formula.t; pob_lvl: 'a level_t}
  [@@deriving compare]

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

  type 'a pob = 'a t

  module X = struct
    type gt = POB : 'a t -> gt
    type t = gt

    include Comparator.Make (struct
      type t = gt

      let compare a b = match (a, b) with POB l, POB r -> my_compare l r
      let sexp_of_t = function _ -> assert false
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
  let pobs {pobs} = pobs
  let level : t -> int = function {lvl= LvlInt n} -> n
  let last = ref 0

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
    let singleton x : t = Set.singleton cmp x

    let compare : t -> t -> int =
     (* TODO: Ask why I should write this shit *)
     fun l r -> Base.Set.compare_m__t (module struct end) l r

    let iter : t -> f:(_ -> unit) -> _ = Base.Set.iter
    let fold : t -> _ = Base.Set.fold
    let add k s : t = Base.Set.add s k
    let remove k set = Base.Set.remove set k
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

  let compare : t -> t -> int =
   (* TODO: Ask why I should write this shit *)
   fun l r -> Base.Set.compare_m__t (module struct end) l r

  let remove : _ key -> t -> t = fun (p, st) s -> Set.remove s (X.P (p, st))
  let add : _ key -> t -> t = fun (p, st) s -> Set.add s (X.P (p, st))
end

module Program = struct
  type t

  let ep _ = assert false
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

type strategy_t =
  {chooseAction: program -> state_set -> pob_state_set -> strategy_rez}

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

module type IFACE = sig
  val propDirSymExec : loc_set -> program -> unit
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
  val nextLevel : ground_level level_t -> unit
  val canReach : Loc.t -> dst:Loc.t -> loc_set -> bool
  val executeInstruction : state -> Loc.t -> state_set
  val mkPrime : Formula.t -> Formula.t
end

module Hardcoded = struct
  let canReach src ~dst locs =
    failwiths "canReach not implemented: %d -> %d" src dst

  module State = struct
    let pM : _ POB.t = POB.create 7 True LvlInf

    let s1 : state =
      State.create ~loc0:2 ~loc:3
        Store.(
          empty
          |> add "x" (Formula.term @@ Term.int 1)
          |> add "y" (Formula.term @@ Term.int 1))
        Formula.True (LvlInt 0)
        POB.Set.(add_exn pM empty)

    let s2 : state =
      State.create ~loc0:3 ~loc:5
        Store.(
          empty
          |> add "x" (Formula.term @@ Term.(add (symb "x") (symb "y")))
          |> add "y" (Formula.term @@ Term.symb "y"))
        Formula.True (LvlInt 0)
        POB.Set.(add_exn pM empty)

    let s3 : state =
      State.create ~loc0:5 ~loc:3
        Store.(
          empty
          |> add "x" (Formula.term @@ Term.(symb "x"))
          |> add "y" (Formula.term @@ Term.symb "x"))
        Formula.True (LvlInt 1)
        POB.Set.(add_exn pM empty)

    let s4 : state =
      State.create ~loc0:3 ~loc:7
        Store.(
          empty
          |> add "x" (Formula.term @@ Term.(symb "x"))
          |> add "y" (Formula.term @@ Term.symb "x"))
        Formula.(le (Term.symb "x") (Term.int 0))
        (LvlInt 0)
        POB.Set.(add_exn pM empty)
  end

  let strat1 : strategy_t =
    let chooseAction _ _ _ = assert false in
    {chooseAction}
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
      with Not_found_s _ -> State.Set.singleton st in
    g.t <- Loc.Map.replace loc next_set g.t

  let blocked_locs g _ = assert false
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
  let choose_action g prog = g.strategy.chooseAction prog g.qf g.qb
end

module IMPL : IFACE = struct
  let init_globals () =
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
    ; strategy= Hardcoded.strat1 }

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
    With_return.with_return (fun r ->
        State.remove_pob s' p' ;
        G.remove_witness g ~key:p' s' ;
        Witnesses.iter_key g.witnesses ~key:p' ~f:(fun s ->
            if State.loc0 s = State.loc0 s' then r.return () ) ;
        G.block_loc g p' (State.loc0 s') ;
        State.Set.iter (Witnesses.find_exn g.witnesses ~key:p') ~f:(fun s ->
            if
              not
                (canReach (State.loc s) ~dst:(POB.loc p') (G.blocked_locs g p'))
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

  let nextLevel _ = assert false
  let executeInstruction _ _ = assert false
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
      let x = Term.symb "x" in
      let x' = x in
      let y = Term.symb "y" in
      let y' = y in
      let _1 = Term.int 1 in
      let _0 = Term.int 0 in
      match State.index st with
      | 1 -> x' = _1 && y' = _1
      | 2 -> (x' = Term.(x + y)) && y' = y
      | 3 -> x' = x && y' = x
      | 4 -> x' <= _0 && x' = x && y' = y
      | _ -> failwith "Should not happen in demo example"

  let start g loc =
    (* Format.eprintf "How to create starting state is mysterious..." ; *)
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
      if canReach (Program.ep prog) ~dst:(POB.loc p') (G.blocked_locs g p') then
        () (*return *)
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

  let propDirSymExec locs prog =
    (* init_globals () ; *)
    let rec loop () =
      if POB.Set.is_empty g.main_pobs then ()
      else
        let () =
          POB.Set.iter g.main_pobs ~f:(fun (POB.X.POB p) ->
              G.add_pob g POB.(create (POB.loc p) Formula.True g.curLvl) ) in
        let rec loop_pobs () =
          match g.strategy.chooseAction prog g.qf g.qb with
          | SRStart loc -> start g loc
          | SRGoFront st -> forward st
          | SRGoBack (p', st') -> backward p' st' prog g.curLvl in
        let () = loop_pobs () in
        g.curLvl <- nextLevel g.curLvl in
    loop () ;
    failwith "TODO: report error"
end
