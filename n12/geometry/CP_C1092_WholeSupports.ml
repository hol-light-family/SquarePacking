(* ========================================================================= *)
(* Port of Compact/Completion/C1092/WholeSupports.lean                        *)
(* (namespace N12Compact.C1092WholeSupports).                                *)
(* lower / upper (ABTransverse) are ABT_lower / ABT_upper.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: formulas *)
let C1092WS_FORMULAS = prove
 (`forall c s u v a nx ny.
     c * c + s * s = &1 /\ &0 < a
     ==> ABT_lower c s u v a nx ny =
           (nx * c + ny * s) * u + (--nx * s + ny * c) * v +
           a * min (nx * c + ny * s) (&0) + a * min (--nx * s + ny * c) (&0) /\
         ABT_upper c s u v a nx ny =
           (nx * c + ny * s) * u + (--nx * s + ny * c) * v +
           a * max (nx * c + ny * s) (&0) + a * max (--nx * s + ny * c) (&0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABT_lower; ABT_upper; tss_support_radius; lcx; lcy] THEN
  SUBGOAL_THEN
   `forall d. a * abs d = a * max d (&0) - a * min d (&0) /\
        a * d = a * max d (&0) + a * min d (&0)`
   (fun th -> MP_TAC(SPEC `nx * c + ny * s` th) THEN
              MP_TAC(SPEC `--nx * s + ny * c` th)) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: lower_nn *)
let C1092WS_LOWER_NN = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ &0 <= e
     ==> ABT_lower c s u v a nx ny = d * u + e * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> min d (&0) = &0`] THEN REAL_ARITH_TAC);;

(* Lean: lower_np *)
let C1092WS_LOWER_NP = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ d <= &0 /\ &0 <= e
     ==> ABT_lower c s u v a nx ny = d * (u + a) + e * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> min d (&0) = &0`;
               REAL_ARITH `d <= &0 ==> min d (&0) = d`] THEN REAL_ARITH_TAC);;

(* Lean: lower_pn *)
let C1092WS_LOWER_PN = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ e <= &0
     ==> ABT_lower c s u v a nx ny = d * u + e * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> min d (&0) = &0`;
               REAL_ARITH `d <= &0 ==> min d (&0) = d`] THEN REAL_ARITH_TAC);;

(* Lean: upper_np *)
let C1092WS_UPPER_NP = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ d <= &0 /\ &0 <= e
     ==> ABT_upper c s u v a nx ny = d * u + e * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`;
               REAL_ARITH `d <= &0 ==> max d (&0) = &0`] THEN REAL_ARITH_TAC);;
