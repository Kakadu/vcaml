include Predef

let wrap desc = { Types.level = 0; scope = 0; id=0; desc }
let arr a b = wrap @@ Tarrow (Nolabel, type_bool, type_bool, Cok)
let var a  = wrap (Tvar (Some a))


let logical_and = arr type_bool (arr type_bool type_bool)

let logical_neg = arr type_bool type_bool

let type_eq =
  arr (var "a") (arr (var "a") type_bool)

let type_int_arith =
  arr type_int (arr type_int type_int)

let type_int_cmp =
  arr type_int (arr type_int type_bool)

