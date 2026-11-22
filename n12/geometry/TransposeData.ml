(* ========================================================================= *)
(* Phase 2: Completion/Cases/C981/TransposeData.lean.                        *)
(* Conventions of DiagonalAuxiliary.ml / VectorData.ml: auxiliaryTranspose j *)
(* is EL j c981da_aux_tr (j < 20), ownerTranspose i is EL i c981da_owner_tr  *)
(* (i < 12), ownership vectors are ((num->bool)list) of length 12,           *)
(* representativeVectors is c981vd_representative_vectors.                   *)
(* transposeAuxiliary s is c981td_tr_aux s = {j | j < 20 /\ EL j aux_tr IN s}*)
(* (the Lean image of Fin.val over the filtered Fin 20);  Lean's v[k]!       *)
(* (default {} out of range) is c981td_getd v k;  List.ofFn over Fin 12 is   *)
(* MAP over [0; ..; 11];  List.flatMap is an ITLIST. Tag C981TD_.          *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/DiagonalAuxiliary.ml";;

(* Lean: transposeAuxiliary *)
let c981td_tr_aux = new_definition
 `c981td_tr_aux (s:num->bool) = {j | j < 20 /\ EL j c981da_aux_tr IN s}`;;

(* Lean: transposeAuxiliary_mem *)
let C981TD_TRANSPOSEAUXILIARY_MEM = prove
 (`forall s j. j < 20 ==> (j IN c981td_tr_aux s <=> EL j c981da_aux_tr IN s)`,
  SIMP_TAC[c981td_tr_aux; IN_ELIM_THM]);;

(* Lean: transposeAuxiliary_subset *)
let C981TD_TRANSPOSEAUXILIARY_SUBSET = prove
 (`forall s. c981td_tr_aux s SUBSET {j | j < 20}`,
  SIMP_TAC[c981td_tr_aux; SUBSET; IN_ELIM_THM]);;

(* Lean: v[k]! on a List (Finset Nat) *)
let c981td_getd = new_definition
 `c981td_getd (v:(num->bool)list) (k:num) = if k < LENGTH v then EL k v else {}`;;

(* Lean: transposeVector *)
let c981td_tr_vector = new_definition
 `c981td_tr_vector (v:(num->bool)list) =
    MAP (\i. c981td_tr_aux (c981td_getd v (EL i c981da_owner_tr)))
        [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]`;;

(* Lean: coveredVectors *)
let c981td_covered_vectors = new_definition
 `c981td_covered_vectors =
    ITLIST (\v acc. CONS v (CONS (c981td_tr_vector v) acc)) c981vd_representative_vectors []`;;

(* basic facts used with the definitions *)
let C981TD_TR_VECTOR_LENGTH = prove
 (`forall v. LENGTH (c981td_tr_vector v) = 12`,
  REWRITE_TAC[c981td_tr_vector; LENGTH_MAP; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let C981TD_TR_VECTOR_EL = prove
 (`forall v i. i < 12
     ==> EL i (c981td_tr_vector v) = c981td_tr_aux (c981td_getd v (EL i c981da_owner_tr))`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[c981td_tr_vector; MAP] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

let C981TD_MEM_COVERED = prove
 (`forall w. MEM w c981td_covered_vectors <=>
       exists v. MEM v c981vd_representative_vectors /\ (w = v \/ w = c981td_tr_vector v)`,
  GEN_TAC THEN REWRITE_TAC[c981td_covered_vectors] THEN
  SPEC_TAC(`c981vd_representative_vectors`, `L:((num->bool)list)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MEM] THEN MESON_TAC[]);;
