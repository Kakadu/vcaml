open Vcore

let heap = Alcotest.testable (GT.fmt Vtypes.heap) (GT.eq Vtypes.heap)

let check_defined () =
  let x = Ident.create "n" in
  let h1 = [x, Heap.cint 2] in (* x:=2 *)
  (* x:= !x + 10 *)
  let h2 = Heap.hsingle x Heap.(binop Vtypes.Plus (li x Predef.type_int) (cint 10) Predef.type_int) in
  let h3 = Heap.hcmps (Vtypes.HDefined h1) h2 in
  (* Format.printf "%a\n%!" (Vtypes.fmt_heap) h3; *)
  let h4 = Heap.write_ident_defined h1 x (Heap.cint 22) in
  (* Format.printf "%a\n%!" (Vtypes.fmt_heap) (HDefined h4); *)
  Alcotest.(check int) "alignement" 5 5;
  Alcotest.(check heap) "heap1" Heap.(hsingle x (cint 12)) h3;
  Alcotest.(check heap) "heap2" Heap.(hsingle x (cint 22)) (HDefined h4);
  ()

let suite =
  [  "heap manipulation",
        [ "denied heaps" , `Quick, check_defined
        ]
  ]

let () = Alcotest.run "cstruct" ( suite)
(* let () = check_alignment () *)
