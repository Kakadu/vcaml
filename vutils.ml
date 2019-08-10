
module List = struct
  include Base.List
  let rec foldk ~f ~(init: 'acc) ~finish = function
    | [] -> finish init
    | x::xs -> f init x xs (fun init -> foldk ~f ~finish ~init xs)

end


open Path
open Typedtree

(* a la first class pattern matching *)
module FCPM = struct
  let is_caml_ref expr ~ok badk =
    match expr.exp_desc with
    | Texp_apply ({exp_desc=Texp_ident(Path.(Pdot (Pident prefix, "ref", _pos)),_,_)}, [(Asttypes.Nolabel, Some e)]) ->
        (* Format.printf "is_caml_ref: %s\n%!" (Ident.name prefix); *)
        if String.equal "Stdlib" (Ident.name prefix)
        then ok e
        else badk ()
    | _ -> badk ()

end
