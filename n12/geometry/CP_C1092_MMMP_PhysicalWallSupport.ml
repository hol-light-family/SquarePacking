(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/PhysicalWallSupport.lean             *)
(* (namespace N12Compact.C1092MMMPPhysicalWallSupport).                      *)
(* Also ports S12.square_support_bound (source/S12/SquareSupportBase.lean);  *)
(* squareRadius q nx ny is tss_support_radius c s a nx ny.  lower: ABT_lower.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/C977WallChains.ml";;

let C1092MPWS_SIGN = prove
 (`forall d. exists p. (p = &1 \/ p = -- &1) /\ p * d = abs d`,
  GEN_TAC THEN ASM_CASES_TAC `&0 <= d` THENL
   [EXISTS_TAC `&1`; EXISTS_TAC `-- &1`] THEN ASM_REAL_ARITH_TAC);;

(* Lean: S12.square_support_bound *)
let C1092MPWS_SQUARE_SUPPORT_BOUND = prove
 (`forall c s u v a nx ny w.
     c * c + s * s = &1 /\ &0 < a /\
     (forall x y. linside c s u v a x y ==> nx * x + ny * y <= w)
     ==> nx * lcx c s u v a + ny * lcy c s u v a + tss_support_radius c s a nx ny <= w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `p:real` (CONJUNCTS_THEN ASSUME_TAC) (SPEC `nx * c + ny * s` C1092MPWS_SIGN) THEN
  X_CHOOSE_THEN `q:real` (CONJUNCTS_THEN ASSUME_TAC) (SPEC `--nx * s + ny * c` C1092MPWS_SIGN) THEN
  REWRITE_TAC[tss_support_radius] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (term_match [] `abs(z:real)`) (rand(concl th))
                 then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (term_match [] `abs(z:real)`) (rand(concl th))
                 then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  MP_TAC(SPECL [`a / &2`; `p * (nx * c + ny * s) + q * (--nx * s + ny * c)`;
                `w - (nx * lcx c s u v a + ny * lcy c s u v a +
                      a / &2 * (p * (nx * c + ny * s) + q * (--nx * s + ny * c)))`]
    C977WC_AFFINE_ENDPOINT) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c * (u + a / &2 + p * (a / &2 - t)) - s * (v + a / &2 + q * (a / &2 - t))`;
    `s * (u + a / &2 + p * (a / &2 - t)) + c * (v + a / &2 + q * (a / &2 - t))`] o
   check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC C977WC_ROT_INSIDE THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lcx; lcy] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN REAL_ARITH_TAC);;

(* Lean: center_bound *)
let C1092MPWS_CENTER_BOUND = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ s <= &0 /\
     (forall x y. linside c s u v a x y ==> x <= &2)
     ==> lcx c s u v a + a * (c - s) / &2 <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `&2`]
    C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID; tss_support_radius] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`;
               REAL_ARITH `s <= &0 ==> abs(-- &1 * s) = --s`] THEN
  REAL_ARITH_TAC);;

(* Lean: lower_le *)
let C1092MPWS_LOWER_LE = prove
 (`forall c s u v a nx ny.
     c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ s <= &0 /\
     (forall x y. linside c s u v a x y ==> x <= &2) /\ &0 <= lcy c s u v a /\
     &0 <= nx /\ ny <= &0
     ==> ABT_lower c s u v a nx ny <=
         &2 * nx - a * (nx * (c - s) + abs(nx * c + ny * s) +
                        abs(--nx * s + ny * c)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPWS_CENTER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= nx * (&2 - a * (c - s) / &2 - lcx c s u v a) /\
                &0 <= --ny * lcy c s u v a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ABT_lower; tss_support_radius] THEN ASM_REAL_ARITH_TAC);;

(* Lean: own_lt *)
let C1092MPWS_OWN_LT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 <= c /\ s <= &0 /\
     (forall x y. linside c s u v a x y ==> x <= &2) /\ &0 <= lcy c s u v a
     ==> u < &2 * c - (&1 + c pow 2 - c * s) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `c:real`; `s:real`]
    C1092MPWS_LOWER_LE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `--c * s + s * c = &0`; REAL_ABS_0] THEN
  ASM_REWRITE_TAC[REAL_ABS_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (a - &1) * (&1 + c pow 2 - c * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= c * --s` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  REAL_ARITH_TAC);;
