(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components05/Queries.lean
   (namespace N12Compact.Completion.OtherCases.C983.Component05Data).
   Literal query data of component 05 (mask 512).  Lean certified_query% n =
   local query n (mq_signature gives Lean's signature); the Exact decide is
   the OCaml check c983c05q_exact (fails on mismatch).  Tag c983c05q_.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c05q_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c05q_exact";;

(* Lean: combinedQueries5 *)
let c983c05q_combinedQueries5 = [717; 676; 692; 684; 699; 720; 677; 694; 685; 700; 722; 670; 690; 705; 671; 706; 673; 708; 672; 707; 674; 709];;
(* Lean: combinedSignatures5 *)
let c983c05q_combinedSignatures5 =
  [(512, 2, [4; 16; 19], [8]);
   (512, 2, [6; 12; 15], [4]);
   (512, 2, [6; 12; 16], [15]);
   (512, 2, [6; 13; 15], [4]);
   (512, 2, [6; 13; 16], [4]);
   (512, 2, [6; 16; 19], [18]);
   (512, 2, [8; 12; 15], [4]);
   (512, 2, [8; 12; 16], [4; 6]);
   (512, 2, [8; 13; 15], [4]);
   (512, 2, [8; 13; 16], [4]);
   (512, 2, [8; 16; 19], [9]);
   (512, 2, [2; 4; 15], [12]);
   (512, 2, [2; 4; 16], [15]);
   (512, 2, [2; 4; 18], [6]);
   (512, 2, [4; 5; 15], [16]);
   (512, 2, [4; 5; 18], [16]);
   (512, 2, [4; 9; 15], [16; 18]);
   (512, 2, [4; 9; 18], [8]);
   (512, 2, [5; 8; 15], [16]);
   (512, 2, [5; 8; 18], [16]);
   (512, 2, [8; 9; 15], [16]);
   (512, 2, [8; 9; 18], [16])];;
(* Lean: combinedExact5 *)
let () = c983c05q_exact c983c05q_combinedSignatures5 c983c05q_combinedQueries5;;
