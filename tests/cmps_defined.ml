open Vcore



let check_alignment () =
  let x = Ident.create "n" in
  let h1 = [x, Heap.cint 2] in 
  let h2 = Heap.hsingle x Heap.(binop Vtypes.Plus (li x Predef.type_int) (cint 10) Predef.type_int) in 
  let h3 = Heap.hcmps (Vtypes.HDefined h1) h2 in 
  Format.printf "%a\n%!" (Vtypes.fmt_heap) h3;
  let h4 = Heap.write_ident_defined h1 x (Heap.cint 22) in
  Format.printf "%a\n%!" (Vtypes.fmt_heap) (HDefined h4);
  Alcotest.(check int) "alignement" 5 5

let suite = 
  [  "alignment", 
        [ "aligned to 4096" , `Quick, check_alignment
        ]
  ]

(* let () = Alcotest.run "cstruct" ( suite) *)
let () = check_alignment ()