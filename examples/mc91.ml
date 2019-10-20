let rec m91 n =
  if n>100 then n-10
  else m91 (m91 (n+11))

[@@@ prop.arg_lt_100      (fun x -> not (x>100) || (m91 x = 91) )]
