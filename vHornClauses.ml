open Base

type varname = int

type index_state = { mutable st_last_index : int }

let make_st () = { st_last_index = 1}
let last_index st = st.st_last_index
let new_index st =
  st.st_last_index <- st.st_last_index+1;
  last_index st

type formula = Format.formatter -> unit
type term = Format.formatter -> unit
type sort = Format.formatter -> unit

(* TODO: can Horn Clause has empty list of premises? *)
type clause = formula option * formula list

let clause ?head fs = (head, fs)

module T = struct
  let int  n fmt = Format.fprintf fmt "%d" n
  let bool b fmt = Format.fprintf fmt "%b" b
  let call_uf s xs fmt =
    Format.fprintf fmt "(%s " s;
    List.iter xs ~f:(fun f  -> f fmt);
    Format.fprintf fmt ") "
end

module F = struct
  let le _ _ = (fun fmt -> ())
  let eq _ _ = (fun fmt -> ())
end

let declare_rel name sorts = fun fmt ->
  Format.fprintf fmt "(declare-rel %s (" name;
  assert (List.length sorts > 0);
  List.iter sorts ~f:(fun f -> f fmt; Format.fprintf fmt " ");
  Format.fprintf fmt ")\n"

module S = struct
  let int fmt  = Format.fprintf fmt "Int"
end

let pp_clauses fmt clauses =
  List.iter clauses ~f:(fun (h,fs) ->
    Format.fprintf fmt "(rule (and ";
    List.iter fs ~f:(fun pp -> pp fmt);
    Format.fprintf fmt ") ";
    let () = match h with
    | Some h -> h fmt
    | None -> Format.fprintf fmt "false"
    in
    Format.fprintf fmt ")\n"
  )
