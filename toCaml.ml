open Base
open Typedtree
open Vtypes
open Vutils

type heap_desc = string
let next_heap_desc =
  let last = ref 0 in
  (fun () -> incr last; string_of_int !last)

type heap_path =
  | HPIdent of heap_loc
  (* Identifier of function *)
  | HPDefined of Vtypes.defined_heap
  | HPArbitrary of Vtypes.heap
  | HPCmps of heap_path * heap_path [@@deriving gt ~options:{compare; fmt}]

(** Queue of scheduled items for `find_sufix` generation *)
module QoF : sig
  type t
  type item = (heap_desc * heap_path * Vtypes.heap)
  val create: unit -> t
  val enqueue: t -> item -> unit
  val dequeue: t -> item option
  val dequeue_exn: t -> item
  val length: t -> int
end = struct
  module X = struct
      type t = heap_path
      include Comparator.Make(struct
        type t = heap_path
        let compare a b = match GT.compare heap_path a b with
        | GT.EQ -> 0
        | GT.GT -> 1
        | GT.LT -> -1
        let sexp_of_t _ = failwiths "not implemented %s %d" __FILE__ __LINE__
      end)
  end

  type item = (heap_desc * heap_path * Vtypes.heap)
  type t =
    { q : item Queue.t
    ; memo : (heap_path, X.comparator_witness) Set.t
    }
  let create () : t =
    let c : (module Comparator.S with
             type comparator_witness = X.comparator_witness and
             type t = heap_path)
      = (module X)
    in
    { q = Queue.init 0 ~f:(fun _ -> assert false)
    ; memo = Set.empty c
    }

  let enqueue { q; memo } ((desc, path, heap) as next) =
    (* we should not schedule processing functions that has been already processed *)
    match path with
    | HPIdent id when Set.mem memo path -> ()
    | _ -> Queue.enqueue q next

  let dequeue { q } = Queue.dequeue q
  let dequeue_exn { q } = Queue.dequeue_exn q
  let length { q } = Queue.length q
end

let exec api texprs =
  Format.printf "ToCaml.exec terms = %a\n%!" (GT.fmt GT.list @@ GT.fmt term) (List.map texprs ~f:fst);
  let open Format in
  let module VHC = VHornClauses.ML in
  let skip_lambdas =
    let rec helper acc = function
      | Vtypes.Lambda { lam_argname = Some n; lam_body; lam_eff } ->
          helper (n::acc) (Heap.hdot lam_eff lam_body)
          (* TODO: Maybe hdot should be done elsewhere *)
      | Vtypes.Lambda { lam_argname = None } ->
          failwith "bad property"
      | t -> (acc, t)
    in
    helper []
  in

  let rec camllizer ~assert_name univ_vars root_prop : VHC.program =
    let univ_vars = List.map univ_vars ~f:MyIdent.to_string in
    let q = QoF.create () in
    let (_: string option) = assert_name in

    let rec do_term root_term =
(*      Format.printf "do_term %a\n%!" (GT.fmt term) root_term;*)
      match root_term with
      | CInt n           -> VHC.E.int n
      | LI (None, Reference(link_id,_), _)
      | Reference (link_id,_) ->
          VHC.E.(app2 (ident "tau") (link link_id))
      | Ident (id, _)
      | LI (None, Ident (id,_), _) ->
          VHC.E.(app2 (ident "tau") (loc (MyIdent.to_string id)))
(*      | LI (None, id, _) -> VHC.E.ident (MyIdent.to_string id)*)
      | LI (None, term, _) -> do_term term
      | LI (Some (HCmps (l,r) as heap), id, _) ->
          let new_desc = next_heap_desc () in
          QoF.enqueue q (new_desc, HPArbitrary heap, heap);
          VHC.E.(
            app2
              (app2 (find new_desc)
                  (ident "tau"))
              (ident "x")
          )
          (* TODO: why "x"?*)
      | LI (Some (HDefined hs), id, _) ->
          let new_desc = next_heap_desc () in
          assert false
      | Call (Builtin BiGT, [a; b], _)
      | Call (Builtin BiLT, [b; a], _) ->
          VHC.E.gt (do_term a) (do_term b)
      | Call (Builtin BiGE, [a; b], _)
      | Call (Builtin BiLE, [b; a], _) ->
          VHC.E.ge (do_term a) (do_term b)
      | Call (Builtin BiNeg, [a], _) ->
          VHC.E.neg (do_term a)
      | Call (Builtin BiAnd, [], _) ->
          failwiths "TODO: %s %d" __FILE__ __LINE__
      | Call (Builtin BiAnd, x::xs, _) ->
          List.map xs ~f:do_term |>
          List.fold_left ~init:(do_term x) ~f:VHC.E.and_
      | Call (Builtin BiStructEq, [a; b], _) ->
          VHC.E.eq (do_term a) (do_term b)

      | Call (Builtin BiPlus, [a; b], _) ->
      (*| Call ( Ident (id,_), [b; a], _) when String.equal (Ident.name id) "+"->*)
          VHC.E.binop "+" (do_term a) (do_term b)

      | Call (LI (_, Ident(fident,_),_), [ LI (_,argid,_) as arg], _) -> begin
          match Heap.Api.find_ident_exn api fident with
          | exception Not_found ->
              Format.printf "%a\n\n%!" Vtypes.fmt_term root_term;
              failwiths "TODO: %s %d" __FILE__ __LINE__
          | (_, Lambda { lam_argname=Some arg_ident; lam_argtype; lam_body; lam_eff }) ->
              (* enqueue argument initialization *)
              let arg_descr = next_heap_desc () in
              let arg_heap = Heap.hsingle (Heap.heap_loc_of_ident arg_ident) arg lam_argtype in
              QoF.enqueue q (arg_descr, HPArbitrary arg_heap, arg_heap);

              let f_descr = next_heap_desc () in
              QoF.enqueue q (f_descr, HPIdent (Heap.heap_loc_of_ident fident), lam_eff);
(*              let t = Heap.hdot arg_heap @@ Heap.hdot lam_eff lam_body in*)
              VHC.E.(app
                  (find (GT.show MyIdent.t fident))
                  [ find arg_descr
(*                  ; ident @@ GT.show MyIdent.t @@ Heap.ident_of_heap_loc_exn argid*)
                  ; do_term argid
                  ]
                  )
              (* TODO: Apply `find` to something?*)
           | _ ->
              failwiths "I don't know what to write here %s %d" __FILE__ __LINE__
        end
      | Union us ->
          List.fold_right us
            ~init: VHC.E.unreachable
            ~f:(fun (guard_term, result_term) acc ->
              let c = do_term guard_term in
              let r = do_term result_term in
              (* TODO: fix non-tail recursion *)
              VHC.E.(ite c r acc)
            )
      (*| Call (Ident (id,_),args,_) ->*)
      | CBool b -> VHC.E.bool b
      | Unreachable -> VHC.E.unreachable
      | _ ->
          Format.printf "\n%a\n%!"   (GT.fmt  Vtypes.term) root_term;
          Format.printf "\n%s\n\n%!" (GT.show Vtypes.term root_term);
          failwiths "TODO: %s %d" __FILE__ __LINE__
    in
    let rec work_queue acc =
      Format.printf "work_queue of length %d.\n%!" (QoF.length q);

      let continue xs = work_queue (xs @ acc) in
      match QoF.dequeue q with
      | None -> VHC.program acc
      | Some (desc, _hp, h) -> Format.printf "working on heap @[%a@]\n%!" (GT.fmt heap) h; match h with
      | HCmps (l,r) ->
          let new_descl = next_heap_desc () in
          let new_descr = next_heap_desc () in
          QoF.enqueue q (new_descl, HPArbitrary l, l);
          QoF.enqueue q (new_descr, HPArbitrary r, r);
          let si =
            VHC.SI.find desc (fun tau x ->
              VHC.E.(app (find new_descl)
                      [ app2 (find new_descr) (ident tau)
                      ; ident x
                      ]))
          in
          work_queue (si :: acc)
      | HDefined xs ->
          let si =
            VHC.SI.find desc (fun tau x ->
              VHC.E.(switch_ident x @@
                List.map xs ~f:(fun (id,(_,t)) -> (Heap.name_of_heap_loc id, do_term t))
              ))
          in
          work_queue (si :: acc)
          (*
      | HCall (Ident (ident,_), [arg]) -> begin
          match Heap.Api.find_ident_exn api ident with
          | exception Not_found ->
              Format.printf "%a\n\n%!" Vtypes.fmt_heap h;
              failwiths "TODO: %s %d" __FILE__ __LINE__
          | (_, Lambda { lam_argname=Some arg_ident; lam_body }) ->
              let new_descr = next_heap_desc () in
              let arg_heap = Heap.hsingle arg_ident arg in
              Queue.enqueue q (new_descr, arg_heap);
              Format.printf "%a\n\n%!" Vtypes.fmt_heap h;
              Format.printf "%a\n\n%!" Vtypes.fmt_term lam_body;
              failwiths "TODO: %s %d" __FILE__ __LINE__
        end
        *)
      | HCall (LI (None, Ident (ident,_),_), [arg]) -> begin
          match Heap.Api.find_ident_exn api ident with
          | exception Not_found ->
              Format.printf "%a\n\n%!" Vtypes.fmt_heap h;
              failwiths "TODO: %s %d" __FILE__ __LINE__
          | (_, Lambda { lam_argname=Some arg_ident; lam_argtype; lam_body; lam_eff }) ->
              let new_descr = next_heap_desc () in
              let arg_heap = Heap.hsingle (Heap.heap_loc_of_ident arg_ident) arg lam_argtype in
              (* enqueue argument initialization *)
              QoF.enqueue q (new_descr, HPArbitrary arg_heap, arg_heap);
              let f_descr = next_heap_desc () in
              QoF.enqueue q (f_descr, HPIdent (Heap.heap_loc_of_ident ident), lam_eff);
              work_queue acc
              (*Format.printf "%a\n\n%!" Vtypes.fmt_heap h;
              Format.printf "%a\n\n%!" Vtypes.fmt_term lam_body;
              failwiths "TODO: %s %d" __FILE__ __LINE__*)
        end
      | HMerge gs -> begin
          match _hp with
          | HPIdent ident ->
            let si =
              VHC.SI.find desc (fun tau x ->
                List.fold_right gs
                  ~init: VHC.E.unreachable
                  ~f:(fun (guard_term, heap) acc ->
                    let c = do_term guard_term in
                    VHC.E.(ite c todo acc)
                  )
                )
            in
            continue [si]
          | _ ->
              failwiths "TODO: %s %d" __FILE__ __LINE__
        end
      | _ ->
          Format.printf "heap path: %a\n%!" (GT.fmt heap_path) _hp;
          Format.printf "%a\n\n%!" Vtypes.fmt_heap h;
          failwiths "TODO: %s %d" __FILE__ __LINE__
    in

    let result_term  = do_term root_prop in

    VHC.join_programs
      [ work_queue []
      ; VHC.program
          [ VHC.SI.assert_ ~name:(Option.value assert_name ~default:"")
              univ_vars result_term ]
      ]
  in

  let clauses =
    VHC.join_programs @@
    List.mapi texprs ~f:(fun n (t, assert_name) ->
      (* Format.printf "%a\n\n%!" Vtypes.fmt_term t; *)
      let (univ_vars, term_body) = skip_lambdas t in
      let f = camllizer ~assert_name univ_vars in
      match term_body with
      | Vtypes.Union xs ->
          VHC.join_programs @@
          List.map xs ~f:(fun (_,t) -> f t)
      | _ ->
          f term_body
    )
  in
  VHC.pp_program Format.std_formatter clauses
