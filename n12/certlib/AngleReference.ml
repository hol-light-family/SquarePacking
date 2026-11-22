(* ========================================================================= *)
(* Port of source/S12/AngleReference.lean (Jatloe, N12-jatloe).              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/AngleEnclosure.ml";;
needs "n12/certlib/ReferenceGeometry.ml";;

(* Lean: AngleEnclosure.reference *)
let ae_reference = new_definition
 `ae_reference w lowerSide = RefSq (ae_c w) (ae_s w) (lowerSide * ae_inner w)`;;

(* Lean: AngleEnclosure.reference_checked *)
let AR_REFERENCE_CHECKED = prove
 (`forall w lowerSide. ae_check w /\ &0 < lowerSide ==> rs_check (ae_reference w lowerSide)`,
  REWRITE_TAC[ae_check; ae_reference; rs_check; rs_c; rs_s; rs_side] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL]);;

(* Lean: AngleEnclosure.inner_sound *)
let AR_INNER_SOUND = prove
 (`forall w lowerSide c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     ae_check w /\ &0 < lowerSide /\ c = normalC t /\ s = normalS t /\
     ae_lower w <= t /\ t <= ae_upper w /\ lowerSide <= a
     ==> forall P. psub P (lcx c s u v a, lcy c s u v a) IN rs_sqset (ae_reference w lowerSide)
             ==> P IN sqset c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RG_REFERENCE_INNER_CONTAINMENT THEN
  ASM_SIMP_TAC[AR_REFERENCE_CHECKED] THEN
  MP_TAC(SPECL [`w:angle_enc`; `t:real`] AE_SUPPORT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ae_reference; rs_c; rs_s; rs_side] THEN
  UNDISCH_TAC `ae_check w` THEN REWRITE_TAC[ae_check] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(normalC t * ae_c w + normalS t * ae_s w) +
                abs(--normalC t * ae_s w + normalS t * ae_c w) =
                abs(ae_c w * normalC t + ae_s w * normalS t) +
                abs(--(ae_s w) * normalC t + ae_c w * normalS t)` SUBST1_TAC THENL
   [BINOP_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`abs(ae_c w * normalC t + ae_s w * normalS t) +
            abs(--(ae_s w) * normalC t + ae_c w * normalS t)`,`B:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`ae_inner w * B <= &1`] THEN NLIN_TAC []);;
