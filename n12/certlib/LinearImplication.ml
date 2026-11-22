(* ========================================================================= *)
(* Port of source/S12/LinearImplication.lean (Jatloe, N12-jatloe).           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/LinearCertificate.ml";;

(* Lean: LinearConstraint.opposite *)
let lc_opposite = define
 `lc_opposite (LinCon f b) = LinCon (aff_scale (-- &1) f) (~b)`;;

(* Lean: LinearConstraint.opposite_holds *)
let LI_OPPOSITE_HOLDS = prove
 (`forall r p. lc_holds (lc_opposite r) p <=> ~lc_holds r p`,
  MATCH_MP_TAC lincon_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lc_opposite; lc_holds; LC_AFF_EVAL_SCALE] THEN
  BOOL_CASES_TAC `a1:bool` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: LinearImplicationCheck *)
let limp_check = new_definition
 `limp_check n inputs target terms <=>
    lcert_check n (CONS (lc_opposite target) inputs) terms`;;

(* Lean: linear_implication_sound *)
let LI_LINEAR_IMPLICATION_SOUND = prove
 (`forall n inputs target terms p.
     limp_check n inputs target terms /\ (forall r. MEM r inputs ==> lc_holds r p)
     ==> lc_holds target p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[limp_check] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LC_LINEAR_CERTIFICATE_SOUND) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `p:real list`) THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[LI_OPPOSITE_HOLDS]);;
