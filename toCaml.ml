open Base
open Typedtree
open Vtypes
open Vutils

type heap_desc = string
let next_heap_desc =
  let last = ref 0 in
  (fun () -> incr last; string_of_int !last)

type heap_path =
  | HPIdent of MyIdent.t
  | HPCmps of heap_path * heap_path [@@deriving gt ~options:{compare}]

module Queue_of_finds : sig
  type t
end = struct
  type comparator_witness
  module C = struct
    type t = heap_path
    type comparator_witness
    let comparator =
      { compare = (fun a b -> GT.compare heap_path a b)
      ; sexp_of_t = (fun _ -> failwith "not implemented")
      }
  end
  type t =
    { q : (heap_desc * heap_path * Vtypes.heap) Queue.t
    ; memo : int
    }
  let create () : t = Queue.init 0 ~f:(fun _ -> assert false)
end
let exec api texprs =
  let open Format in
  let module VHC = VHornClauses.ML in
  let skip_lambdas =
    let rec helper acc = function
      | Vtypes.Lambda { lam_argname = Some n; lam_body } ->
          helper (n::acc) lam_body
      | Vtypes.Lambda { lam_argname = None } ->
          failwith "bad property"
      | t -> (acc, t)
    in
    helper []
  in

  let rec camllizer ~assert_name univ_vars root_prop : VHC.program =
    let univ_vars = List.map univ_vars ~f:MyIdent.to_string in
    let q = Queue.init 0 ~f:(fun _ -> assert false) in
    let (_: (heap_desc * Vtypes.heap) Queue.t) = q in
    let (_: string option) = assert_name in

    let rec do_term term = match term with
      | CInt n           -> VHC.E.int n
      | LI (None, id, _) -> VHC.E.ident (MyIdent.to_string id)
      | LI (Some (HCmps (l,r) as heap), id, _) ->
          let new_desc = next_heap_desc () in
          Queue.enqueue q (new_desc, heap);
          VHC.E.(
            app2
              (app2 (find new_desc)
                  (ident "tau"))
              (ident "x")
          )
      | LI (Some (HDefined hs), id, _) ->
          let new_desc = next_heap_desc () in
          assert false
      | Call (Builtin (BiGT, _), [a; b], _)
      | Call (Builtin (BiLT, _), [b; a], _) ->
          VHC.E.gt (do_term a) (do_term b)
      | _ ->
          Format.printf "%a\n\n%!" Vtypes.fmt_term term;
          failwiths "TODO: %s %d" __FILE__ __LINE__
    in
    let rec work_queue acc =
      match Queue.dequeue q with
      | None -> VHC.program acc
      | Some (desc, h) -> match h with
      | HCmps (l,r) ->
          let new_descl = next_heap_desc () in
          let new_descr = next_heap_desc () in
          Queue.enqueue q (new_descl, l);
          Queue.enqueue q (new_descr, r);
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
                List.map xs ~f:(fun (id,t) -> (Ident.name id, do_term t))
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
      | HCall (LI (None,ident,_), [arg]) -> begin
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
      | _ ->
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
