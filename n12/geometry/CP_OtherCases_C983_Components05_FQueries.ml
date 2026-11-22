(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components05/FQueries.lean
   (namespace N12Compact.Completion.OtherCases.C983.Component05Data).
   Literal query data of component 05 (mask 512).  Lean certified_query% n =
   local query n (mq_signature gives Lean's signature); the Exact decide is
   the OCaml check c983c05fq_exact (fails on mismatch).  Tag c983c05fq_.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c05fq_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c05fq_exact";;

(* Lean: fQueries5 *)
let c983c05fq_fQueries5 = [582; 583; 585; 588; 595; 605; 618; 592; 586; 594; 603];;
(* Lean: fSignatures5 *)
let c983c05fq_fSignatures5 =
  [(512, 0, [0], [2; 4]);
   (512, 0, [1], [5]);
   (512, 0, [2], [4]);
   (512, 0, [3], [7]);
   (512, 0, [5], [4; 8]);
   (512, 0, [7], []);
   (512, 0, [9], [4; 8]);
   (512, 0, [0; 4], [5]);
   (512, 0, [0; 2], []);
   (512, 0, [3; 4], [5]);
   (512, 0, [3; 6], [5])];;
(* Lean: fExact5 *)
let () = c983c05fq_exact c983c05fq_fSignatures5 c983c05fq_fQueries5;;
