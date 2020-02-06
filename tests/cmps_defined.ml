open Vcore

let heap = Alcotest.testable (GT.fmt Vtypes.heap) (GT.eq Vtypes.heap)
let term = Alcotest.testable (GT.fmt Vtypes.term) (GT.eq Vtypes.term)

let type_dummy = Predef.type_int

let check_defined () =
  let x = Ident.create "n" in
  let h1 = [x, Heap.cint 2] in (* x:=2 *)
  (* x:= !x + 10 *)
  let h2 =
    Heap.(hsingle x
      (binop (builtin Vtypes.BiPlus type_dummy) (li x Predef.type_int) (cint 10)
        Predef.type_int))
  in
  let h3 = Heap.hcmps (Vtypes.HDefined h1) h2 in
  (* Format.printf "%a\n%!" (Vtypes.fmt_heap) h3; *)
  let h4 = Heap.write_ident_defined h1 x (Heap.cint 22) in
  (* Format.printf "%a\n%!" (Vtypes.fmt_heap) (HDefined h4); *)
  Alcotest.(check int) "alignment" 5 5;
  Alcotest.(check heap) "heap1" Heap.(hsingle x (cint 12)) h3;
  Alcotest.(check heap) "heap2" Heap.(hsingle x (cint 22)) (HDefined h4);
  ()

let add_union_to_defined () =
  let open Heap in
  (* x < 10 *)
  let ph1 =
    let x = Ident.create "x" in
    pf_term
      (binop (builtin Vtypes.BiPlus type_dummy) (li x Predef.type_int) (cint 10)
        Predef.type_int)
  in
  let ph2 = pf_not ph1 in
  let u = union
    [ (ph1, cint 10)
    ; (ph2, cint 20)
    ]
  in
  let is_union = function Vtypes.Union  _ -> true | _ -> false in
  let is_merge = function Vtypes.HMerge _ -> true | _ -> false in
  Alcotest.(check bool) "is union 1" true (is_union u);
  let h = hsingle (Ident.create "y") u in
  Alcotest.(check bool) "is merge 1" true (is_merge h);
  ()

let suite =
  [  "heap_manip",
        [ "defined heaps",     `Quick, check_defined
        ; "siplifying unions", `Quick, add_union_to_defined
        ]
  ]

let () = Alcotest.run "vcaml" ( suite)

