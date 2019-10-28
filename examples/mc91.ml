let rec m91 n =
  if n>100 then n-10
  else m91 (m91 (n+11))

(* argument of attribute should not happen *)
[@@@ prop.arg_lt_100      (fun x -> (x<=100) && not (m91 x =   91) )]
(* [@@@ prop.arg_lt_100      (fun x -> (x>100)  && not (m91 x = n-10) )] *)
