(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLeftBelowMargin.lean.          *)
(* Lower relative-angle branch of the left-square support inequality.        *)
(* Lean variables C S of `margin` are named cc ss here.                      *)
(* alpha = l*cc + r*ss, k = l*ss - r*cc, D = 1 - cc + 2/5*ss written out.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let FAWPLBM_NEG_OF_MUL = prove
 (`forall k x. &0 < k /\ k * x < &0 ==> x < &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: margin *)
let FAWPLBM_MARGIN = prove
 (`forall l r cc ss u.
     c977cc_normal l r /\ c977cc_normal cc ss /\
     &4 / &25 <= r /\ ss <= &11 / &50 /\
     &0 <= u /\ u <= &1 / &1000 /\ r * cc - l * ss <= &0
     ==> &2 - (&543 / &500) * r pow 2 - l * (&1 + (l * cc + r * ss)) +
         l * (r * cc - l * ss) * (&1 - cc + (&2 / &5) * ss) +
         l * (l * cc + r * ss) * u <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cc:real`; `ss:real`; `l:real`; `r:real`] C977CSB_SINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cc:real`; `ss:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `cc:real`; `ss:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&97 / &100 <= cc` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (&11 / &50 - ss) * (&11 / &50 + ss) /\
                 &0 <= (&97 / &100 - cc) * (&97 / &100 + cc)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `cc pow 2 + ss pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l * cc + r * ss` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `l * ss - r * cc <= (&2 / &5) * ss` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= cc * (r - &4 / &25) /\ &0 <= ss * (&1 - l)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(l * cc + r * ss) pow 2 + (l * ss - r * cc) pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN
   UNDISCH_TAC `cc pow 2 + ss pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (l * cc + r * ss) * (&1 - (l * cc + r * ss)) /\
    &0 <= (l * ss - r * cc) * ((&1 - cc + (&2 / &5) * ss) - (l * ss - r * cc))`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= l * ((l * ss - r * cc) * (&1 - cc + (&2 / &5) * ss) -
               (&1 - (l * cc + r * ss))) /\
    &0 <= (l * (&1 - (l * cc + r * ss))) * u`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   (CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]) THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 - (&543 / &500) * r pow 2 - &2 * l + l * u < &0` ASSUME_TAC THENL
  [MATCH_MP_TAC FAWPLBM_NEG_OF_MUL THEN EXISTS_TAC `&1 + l` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + l) * (&2 - (&543 / &500) * r pow 2 - &2 * l + l * u) =
                 r pow 2 * (&2 - (&543 / &500) * (&1 + l)) + l * (&1 + l) * u`
   SUBST1_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN
    `&0 <= r pow 2 * ((&543 / &500) * (&1 + l) - &2 - &13 / &100) /\
     &0 <= (r - &4 / &25) * (r + &4 / &25) /\
     &0 <= (l * (&1 + l)) * (&1 / &1000 - u) /\
     &0 <= (&1 - l) * (l + &2)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&2 - (&543 / &500) * r pow 2 - &2 * l + l * u < &0` THEN
  UNDISCH_TAC `&0 <= l * ((l * ss - r * cc) * (&1 - cc + (&2 / &5) * ss) -
               (&1 - (l * cc + r * ss)))` THEN
  UNDISCH_TAC `&0 <= (l * (&1 - (l * cc + r * ss))) * u` THEN
  REAL_ARITH_TAC);;
