(* ========================================================================= *)
(* Port of Compact/Completion/C981/SupportForms.lean                          *)
(* (N12Compact.C981CompletionSupportForms).  Band formulas of the support    *)
(* function of an actual square.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: upper_in_bands *)
let C981SF_UPPER_IN_BANDS = prove
 (`forall c s u v a nx ny.
     ABT_upper c s u v a nx ny =
       (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) +
       a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: lower_in_bands *)
let C981SF_LOWER_IN_BANDS = prove
 (`forall c s u v a nx ny.
     ABT_lower c s u v a nx ny =
       (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) -
       a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: lower_negative_pos *)
let C981SF_LOWER_NEGATIVE_POS = prove
 (`forall c s u v a t nx ny.
     s = --t /\ &0 <= nx * c - ny * t /\ &0 <= nx * t + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c - ny * t) * u + (nx * t + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(nx * c + ny * --t) = nx * c - ny * t /\
                abs(--nx * --t + ny * c) = nx * t + ny * c`
  (fun th -> REWRITE_TAC[th]) THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;
