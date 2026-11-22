(* ========================================================================= *)
(* Driver for layer 11: the 41 diagonal rows, the 103 domain specs, the 419  *)
(* core proofs, and the reduction to the 117 retained rows.                  *)
(* ========================================================================= *)

needs "n12/phase1/step6.ml";;

let DIAG_ROWS = map (fun i -> i, diagonal_row_thm i)
  (filter (fun i -> exists diag_bad (row_masks i)) (0--576));;

List.iter (fun (i,m,k,lo,hi,al) -> Hashtbl.replace SPEC_TBL i (spec_theorem m k lo hi al))
  SINGLE_SPECS;;

let CORE_TBL = Hashtbl.create 500;;
List.iter (fun ((cid,_,_,_) as c) -> Hashtbl.replace CORE_TBL cid (core_theorem c)) CORES;;

let PACKING_117 = reduction_117 DIAG_ROWS CORE_TBL;;

let S12_REDUCED_117 = prove
 (`forall t. packs 12 t /\ t < &4
       ==> exists c1 c2 a b l r. NPACK c1 c2 a b l /\ MEM r RETAINED /\
                           IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PACKS12_NORMALIZE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num->real` (X_CHOOSE_THEN `c2:num->real` (X_CHOOSE_THEN `a:num->real`
    (X_CHOOSE_THEN `b:num->real` (X_CHOOSE_THEN `l:real` ASSUME_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PACKING_117) THEN MESON_TAC[]);;
