(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components05/GQueries.lean
   (namespace N12Compact.Completion.OtherCases.C983.Component05Data).
   Literal query data of component 05 (mask 512).  Lean certified_query% n =
   local query n (mq_signature gives Lean's signature); the Exact decide is
   the OCaml check c983c05gq_exact (fails on mismatch).  Tag c983c05gq_.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c05gq_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c05gq_exact";;

(* Lean: gQueries5 *)
let c983c05gq_gQueries5 = [626; 627; 629; 632; 636; 647; 661; 654];;
(* Lean: gSignatures5 *)
let c983c05gq_gSignatures5 =
  [(512, 1, [0], []);
   (512, 1, [1], [0]);
   (512, 1, [2], [5; 6]);
   (512, 1, [3], [5; 6]);
   (512, 1, [4], [3]);
   (512, 1, [7], [6; 9]);
   (512, 1, [9], [6]);
   (512, 1, [6; 7], [3])];;
(* Lean: gExact5 *)
let () = c983c05gq_exact c983c05gq_gSignatures5 c983c05gq_gQueries5;;
