let rec m91 n =
  if n>100 then n-10
  else m91 (m91 (n+11))


(** Intuition:
            Invariant is A => B
   But here we encode cases which should never happen (satisfabilty leads
   to an error). Se we write `A & not B` instead of implication
*)

(* argument of attribute should not happen *)
[@@@ prop.arg_lt_100      (fun x -> (x<=100) && not (m91 x =   91) )]
(* i.e. is x<=100 then always (m91 x = 91) *)

[@@@ prop.arg_lt_100      (fun x -> (x>100)  && not (m91 x = x-10) )]
(* i.e. if arg > 100 then always (m91 x = n-10) *)
