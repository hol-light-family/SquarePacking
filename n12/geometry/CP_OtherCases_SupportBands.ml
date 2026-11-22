(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SupportBands.lean (Jatloe,          *)
(* N12-jatloe; namespace N12Compact.Completion.OtherCases.SupportBands).     *)
(* Full-square lower supports in face coordinates.  Lean lower is ABT_lower; *)
(* q.side_pos is the explicit hypothesis &0 < a.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

(* Lean: lower_pn *)
let OCSB_LOWER_PN = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ --nx * s + ny * c <= &0
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: lower_nn *)
let OCSB_LOWER_NN = prove
 (`forall c s u v a nx ny. nx * c + ny * s <= &0 /\ --nx * s + ny * c <= &0
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`] THEN REAL_ARITH_TAC);;

(* Lean: lower_bound_pn *)
let OCSB_LOWER_BOUND_PN = prove
 (`forall c s u v a nx ny. &0 < a /\ --nx * s + ny * c <= &0
     ==> ABT_lower c s u v a nx ny <=
         (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  MP_TAC(SPEC `nx * c + ny * s` REAL_ABS_LE) THEN
  ABBREV_TAC `P = nx * c + ny * s` THEN ABBREV_TAC `Q = --nx * s + ny * c` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `abs P - P`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;
