(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCentersScalars.lean   *)
(* (N12Compact.C1092MPPMMissingNegativeCenters).  Continuous support        *)
(* margins of MISSING-NEGATIVE-BOUNDARIES, Theorems 2-3.                    *)
(* Normal: c977cc_normal; Quarter: c1092mcs_quarter; half: c1092mcbh_half;   *)
(* cosH / sinH: c1092sps_cosH / c1092sps_sinH; QuadraticArc.X / Y / Z /     *)
(* remainder / value / nonnegative: c1092mpqa_* / C1092MPQA_NONNEGATIVE;     *)
(* Envelopes bottomValue / leftValue / circle_order(_reverse) /              *)
(* bottom_difference / left_difference: c1092mpbes_* / C1092MPBES_*;         *)
(* cosine_order: C977CSB_COSINE_ORDER; large_sum: C1092MMNCE_LARGE_SUM;      *)
(* steep_bounds (CrosspointSupport): C1092G10_STEEP_BOUNDS;                  *)
(* UnitCircleChord.decreasing: CCUCC_DECREASING.  Tag C1092MNCS_.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointEnvelope.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopesScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;

(* Lean: Fb, Fl, bottomPlusA .. leftMinusB (definitions) *)
let c1092mncs_Fb = new_definition
 `c1092mncs_Fb (c:real) (s:real) = &3 / &2 - (&4 / &5) * c - &2 * s + s * (c + s) / &2`;;
let c1092mncs_Fl = new_definition
 `c1092mncs_Fl (c:real) (s:real) = &3 / &2 - (&36 / &25) * c - (&6 / &5) * s + c * (c + s) / &2`;;
let c1092mncs_bottomPlusA = new_definition
 `c1092mncs_bottomPlusA (c:real) (s:real) = c - s - &4 / &5 + (&37 / &50) * s pow 2`;;
let c1092mncs_bottomPlusB = new_definition
 `c1092mncs_bottomPlusB (c:real) (s:real) = c + s - &2 - (&37 / &50) * c * s`;;
let c1092mncs_bottomMinusA = new_definition
 `c1092mncs_bottomMinusA (c:real) (s:real) = c - &4 / &5 + (&13 / &20) * s pow 2 - (&7 / &20) * c * s`;;
let c1092mncs_bottomMinusB = new_definition
 `c1092mncs_bottomMinusB (c:real) (s:real) = --(&2) + s + (&7 / &20) * c pow 2 - (&13 / &20) * c * s`;;
let c1092mncs_leftPlusA = new_definition
 `c1092mncs_leftPlusA (c:real) (s:real) = c - &36 / &25 - (&21 / &100) * s pow 2 - (&13 / &20) * c * s`;;
let c1092mncs_leftPlusB = new_definition
 `c1092mncs_leftPlusB (c:real) (s:real) = s - (&13 / &20) * s pow 2 - &11 / &20 + (&21 / &100) * c * s`;;
let c1092mncs_leftMinusA = new_definition
 `c1092mncs_leftMinusA (c:real) (s:real) = c + s - &36 / &25 - (&3 / &10) * s pow 2 - c * s`;;
let c1092mncs_leftMinusB = new_definition
 `c1092mncs_leftMinusB (c:real) (s:real) = s - c - s pow 2 + (&3 / &10) * c * s - &1 / &5`;;

let C1092MNCS_DEFS = [c1092mncs_Fb; c1092mncs_Fl; c1092mncs_bottomPlusA; c1092mncs_bottomPlusB;
  c1092mncs_bottomMinusA; c1092mncs_bottomMinusB; c1092mncs_leftPlusA; c1092mncs_leftPlusB;
  c1092mncs_leftMinusA; c1092mncs_leftMinusB];;

let C1092MNCS_LP hs = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false hs;;

(* Lean: bounds *)
let C1092MNCS_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &252 / &373 <= s
     ==> &7 / &10 < c /\ c <= &369 / &500 /\ &27 / &40 <= s /\ s <= &71 / &100 /\
         &9 / &20 <= s pow 2 /\ s pow 2 <= &1 / &2 /\ c pow 2 <= &11 / &20 /\
         &49 / &100 <= c * s /\ c * s <= &1 / &2 /\ &141 / &100 <= c + s /\
         c + s <= &283 / &200 /\ &0 <= c - s /\ c - s <= &31 / &500`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&275 / &373`; `&252 / &373`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `&3 / &5 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MMNCE_LARGE_SUM) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  SUBGOAL_THEN `&0 <= (c - s) * (c + s) /\ &0 <= (s - &27 / &40) * (s + &27 / &40) /\
                &0 <= (c + s - &141 / &100) * (c + s + &141 / &100)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MNCS_LP [SQ_NONNEG `c - s:real`]);;

let C1092MNCS_BOUNDS_TAC =
  FIRST_ASSUM(fun th -> if can (term_match [] `c977cc_normal c s`) (concl th)
    then MP_TAC(SPECL [`c:real`; `s:real`] C1092MNCS_BOUNDS) THEN
         MP_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
         MP_TAC(REWRITE_RULE[c977cc_normal] th) THEN ASM_REWRITE_TAC[]
    else NO_TAC) THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

(* Lean: central_margins *)
let C1092MNCS_CENTRAL_MARGINS = prove
 (`forall c s. c977cc_normal c s /\ &252 / &373 <= s
     ==> &19 / &1000 <= c1092mncs_Fb c s /\ &13 / &100 <= c1092mncs_Fl c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCS_BOUNDS_TAC THEN
  SUBGOAL_THEN `&0 <= (c - s) * (&3 / &5 - c / &2) /\ &0 <= (c - s) * (s / &2 - &3 / &25)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mncs_Fb; c1092mncs_Fl] THEN C1092MNCS_LP []);;

(* Lean: coefficient_bounds *)
let C1092MNCS_COEFFICIENT_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &252 / &373 <= s
     ==> &0 <= c1092mncs_bottomMinusA c s /\ c1092mncs_bottomMinusB c s <= --(&7 / &5) /\
         c1092mncs_leftPlusA c s <= --(&111 / &100) /\ --(&1 / &10) <= c1092mncs_leftPlusB c s /\
         --(&7 / &10) <= c1092mncs_leftMinusA c s /\ c1092mncs_leftMinusB c s <= --(&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCS_BOUNDS_TAC THEN
  REWRITE_TAC C1092MNCS_DEFS THEN C1092MNCS_LP []);;

(* Lean: aligned *)
let C1092MNCS_ALIGNED = prove
 (`forall c s. c977cc_normal c s
     ==> c1092mpbes_bottomValue (&1) (c1092mncs_bottomPlusA c s) (c1092mncs_bottomPlusB c s) c s =
           c1092mncs_Fb c s /\
         c1092mpbes_bottomValue (&1) (c1092mncs_bottomMinusA c s) (c1092mncs_bottomMinusB c s) c s =
           c1092mncs_Fb c s /\
         c1092mpbes_leftValue (&1) (c1092mncs_leftPlusA c s) (c1092mncs_leftPlusB c s) c s =
           c1092mncs_Fl c s /\
         c1092mpbes_leftValue (&1) (c1092mncs_leftMinusA c s) (c1092mncs_leftMinusB c s) c s =
           c1092mncs_Fl c s`,
  REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC([c1092mpbes_bottomValue; c1092mpbes_leftValue] @ C1092MNCS_DEFS) THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: swapped_remainder (private) *)
let C1092MNCS_SWAPPED_REMAINDER = prove
 (`forall z R. &0 <= z /\ z <= &1 / &2 /\ &0 <= R /\ R <= &1 / &2
     ==> &0 <= c1092mpqa_remainder (&1 / &2) (&1 / &2) (&1 / &2) (&0) z R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092mpqa_remainder (&1 / &2) (&1 / &2) (&1 / &2) (&0) z R =
                z + R - z pow 2 - R pow 2 - z * R - z pow 2 * R pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y; c1092mpqa_Z;
                c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z * z <= &1 / &2 * z /\ R * R <= &1 / &2 * R /\ z * R <= z * (&1 / &2) /\
                z * R <= &1 / &2 * R /\ z * R <= &1 / &2 * &1 / &2 /\ &0 <= z * R`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[REAL_ARITH `&1 / &2 * &1 / &2 = (&1 / &2) * (&1 / &2)`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z * R) * (z * R) <= (&1 / &2 * &1 / &2) * (z * R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092MNCS_LP []);;

let C1092MNCS_DIV_LE = prove
 (`forall x y a b. &0 < a /\ &0 < b /\ x * b <= y * a ==> x / a <= y / b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `y / b * a = (y * a) / b`] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let C1092MNCS_COSH0 = prove
 (`c1092sps_cosH (&0) = &1 /\ c1092sps_sinH (&0) = &0`,
  REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let C1092MNCS_QUARTER_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter h t`) o concl));;

(* Lean: bottom_plus *)
let C1092MNCS_BOTTOM_PLUS = prove
 (`forall c s h t. c977cc_normal c s /\ &252 / &373 <= s /\ c1092mcs_quarter h t /\ &0 <= c * t - s * h
     ==> &0 < c1092mpbes_bottomValue (&1) (c1092mncs_bottomPlusA c s) (c1092mncs_bottomPlusB c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCS_BOUNDS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MNCS_CENTRAL_MARGINS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MNCS_ALIGNED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MNCS_QUARTER_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `h:real`; `t:real`] C1092MPBES_CIRCLE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`t:real`; `h:real`] C1092MCBH_QUARTER_HALF) THEN
  MP_TAC(SPECL [`s:real`; `c:real`] C1092MCBH_QUARTER_HALF) THEN
  REWRITE_TAC[c1092mcs_quarter] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `c1092mcbh_half t h <= c1092mcbh_half s c /\ c1092mcbh_half s c <= &1 / &2`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcbh_half] THEN CONJ_TAC THENL
     [MATCH_MP_TAC C1092MNCS_DIV_LE THEN
      SUBGOAL_THEN `&0 <= (c - h) * (&1 + s) /\ &0 <= c * (t - s)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
      RASM_ARITH_TAC;
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= s ==> &0 < &1 + s`; ASSUME `&0 <= s`] THEN
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + c1092mncs_bottomPlusB c s` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_bottomPlusB] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists m. &0 < m /\ m <= c1092mncs_Fb c s /\ m <= &1 + c1092mncs_bottomPlusB c s`
    STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (c1092mncs_Fb c s) (&1 + c1092mncs_bottomPlusB c s)` THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c1092mcbh_half t h`; `c1092mcbh_half s c`] C1092MNCS_SWAPPED_REMAINDER) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mpqa_Z (&0) (c1092mcbh_half t h) (c1092mcbh_half s c)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpqa_Z] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &1 + x pow 2 <=> &0 <= &1 + x pow 2`] THEN
    MP_TAC(SPEC `c1092mcbh_half t h` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `c1092mcbh_half s c` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 / &2`; `&1 / &2`; `&1 / &2 - m`; `c1092mncs_bottomPlusB c s`;
                `c1092mncs_bottomPlusA c s`; `&0`; `c1092mcbh_half t h`; `c1092mcbh_half s c`]
    C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&0 <= m * c1092mpqa_Z (&0) (c1092mcbh_half t h) (c1092mcbh_half s c)`
        MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 <= c1092mpqa_remainder (&1 / &2) (&1 / &2) (&1 / &2) (&0)
                     (c1092mcbh_half t h) (c1092mcbh_half s c)` THEN
      REWRITE_TAC[c1092mpqa_remainder] THEN REAL_ARITH_TAC;
      REWRITE_TAC[c1092mpqa_value; C1092MNCS_COSH0] THEN RASM_ARITH_TAC;
      ASM_REWRITE_TAC[c1092mpqa_value] THEN
      UNDISCH_TAC `c1092mpbes_bottomValue (&1) (c1092mncs_bottomPlusA c s) (c1092mncs_bottomPlusB c s) c s =
                   c1092mncs_Fb c s` THEN
      REWRITE_TAC[c1092mpbes_bottomValue] THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value; c1092mpbes_bottomValue] THEN RASM_ARITH_TAC);;

(* the order facts on the quarter circle (circle_order / circle_order_reverse at (s, c)) *)
let C1092MNCS_ORDER_TAC rev =
  MP_TAC(SPECL [`s:real`; `c:real`; `h:real`; `t:real`]
    (if rev then C1092MPBES_CIRCLE_ORDER_REVERSE else C1092MPBES_CIRCLE_ORDER)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC];;

let C1092MNCS_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCS_BOUNDS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MNCS_CENTRAL_MARGINS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MNCS_ALIGNED) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MNCS_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MNCS_QUARTER_TAC;;

(* from  H * (V h t - V c s) = (t - s) * D  and the sign of (t - s) * D, with H > 0 *)
let C1092MNCS_DIFF_TAC diff A B =
  MP_TAC(SPECL [`&1`; A; B; `h:real`; `t:real`; `c:real`; `s:real`] diff) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC;;

(* Lean: bottom_minus *)
let C1092MNCS_BOTTOM_MINUS = prove
 (`forall c s h t. c977cc_normal c s /\ &252 / &373 <= s /\ c1092mcs_quarter h t /\ c * t - s * h <= &0
     ==> &0 < c1092mpbes_bottomValue (&1) (c1092mncs_bottomMinusA c s) (c1092mncs_bottomMinusB c s) h t`,
  C1092MNCS_SETUP_TAC THEN C1092MNCS_ORDER_TAC true THEN
  SUBGOAL_THEN `h <= &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
   `(h + c) / &2 * ((t + s) / &2 + ((h + c) / &2) / &2 - &7 / &5) <= &0 /\
    &0 <= c1092mncs_bottomMinusA c s * ((t + s) / &2) /\
    c1092mncs_bottomMinusB c s * ((h + c) / &2) <= --(&7 / &5) * ((h + c) / &2)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h + c) / &2 * (t + s) / &2 + (((h + c) / &2) pow 2 - ((t + s) / &2) pow 2) / &2 -
    c1092mncs_bottomMinusA c s * ((t + s) / &2) + c1092mncs_bottomMinusB c s * ((h + c) / &2) <= &0`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false [SQ_NONNEG `(t + s) / &2`]; ALL_TAC] THEN
  C1092MNCS_DIFF_TAC C1092MPBES_BOTTOM_DIFFERENCE
    `c1092mncs_bottomMinusA c s` `c1092mncs_bottomMinusB c s` THEN
  SUBGOAL_THEN `&0 <= (h + c) / &2 *
     (c1092mpbes_bottomValue (&1) (c1092mncs_bottomMinusA c s) (c1092mncs_bottomMinusB c s) h t -
      c1092mpbes_bottomValue (&1) (c1092mncs_bottomMinusA c s) (c1092mncs_bottomMinusB c s) c s)`
    MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&0 <= (t - s) * d <=> &0 <= (s - t) * --d`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&0 < c /\ &0 <= h ==> &0 < (h + c) / &2`;
           ASSUME `&0 <= h`; REAL_ARITH `&7 / &10 < c ==> &0 < c`; ASSUME `&7 / &10 < c`] THEN
  RASM_ARITH_TAC);;

(* Lean: sloping_cap (private) *)
let C1092MNCS_SLOPING_CAP = prove
 (`forall c s h t. c977cc_normal c s /\ &252 / &373 <= s /\ c1092mcs_quarter h t /\ s <= t
     ==> h + t / &2 <= &27 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCS_BOUNDS_TAC THEN C1092MNCS_QUARTER_TAC THEN
  MP_TAC(SPECL [`&275 / &373`; `&252 / &373`; `c:real`; `s:real`; `&1`; `&1 / &2`] CCUCC_DECREASING) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `t:real`; `&1`; `&1 / &2`] CCUCC_DECREASING) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN RASM_ARITH_TAC);;

(* Lean: left_plus *)
let C1092MNCS_LEFT_PLUS = prove
 (`forall c s h t. c977cc_normal c s /\ &252 / &373 <= s /\ c1092mcs_quarter h t /\ &0 <= c * t - s * h
     ==> &0 < c1092mpbes_leftValue (&1) (c1092mncs_leftPlusA c s) (c1092mncs_leftPlusB c s) h t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `h + t / &2 <= &27 / &25 /\ c + s / &2 <= &27 / &25` MP_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN CONJ_TAC THEN MATCH_MP_TAC C1092MNCS_SLOPING_CAP THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal c s` THEN UNDISCH_TAC `c1092mcs_quarter h t` THEN
    UNDISCH_TAC `&0 <= c * t - s * h` THEN
    REWRITE_TAC[c977cc_normal; c1092mcs_quarter] THEN REPEAT STRIP_TAC THEN
    TRY(ASM_REAL_ARITH_TAC) THEN
    MP_TAC(SPECL [`s:real`; `c:real`; `h:real`; `t:real`] C1092MPBES_CIRCLE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`t:real`, `t:real`) THEN SPEC_TAC(`h:real`, `h:real`) THEN
  SPEC_TAC(`s:real`, `s:real`) THEN SPEC_TAC(`c:real`, `c:real`) THEN
  REWRITE_TAC[IMP_IMP] THEN C1092MNCS_SETUP_TAC THEN C1092MNCS_ORDER_TAC false THEN
  SUBGOAL_THEN
   `c1092mncs_leftPlusA c s * ((t + s) / &2) <= --(&111 / &100) * ((t + s) / &2) /\
    --(&1 / &10) * ((h + c) / &2) <= c1092mncs_leftPlusB c s * ((h + c) / &2) /\
    &0 <= (t + s) / &2 * (&27 / &25 - (h + c) / &2 - ((t + s) / &2) / &2)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= --((h + c) / &2) * (t + s) / &2 + (((h + c) / &2) pow 2 - ((t + s) / &2) pow 2) / &2 -
    c1092mncs_leftPlusA c s * ((t + s) / &2) + c1092mncs_leftPlusB c s * ((h + c) / &2)`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false [SQ_NONNEG `(h + c) / &2 - &1 / &10`]; ALL_TAC] THEN
  C1092MNCS_DIFF_TAC C1092MPBES_LEFT_DIFFERENCE
    `c1092mncs_leftPlusA c s` `c1092mncs_leftPlusB c s` THEN
  SUBGOAL_THEN `&0 <= (h + c) / &2 *
     (c1092mpbes_leftValue (&1) (c1092mncs_leftPlusA c s) (c1092mncs_leftPlusB c s) h t -
      c1092mpbes_leftValue (&1) (c1092mncs_leftPlusA c s) (c1092mncs_leftPlusB c s) c s)`
    MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&0 < c /\ &0 <= h ==> &0 < (h + c) / &2`;
           ASSUME `&0 <= h`; REAL_ARITH `&7 / &10 < c ==> &0 < c`; ASSUME `&7 / &10 < c`] THEN
  RASM_ARITH_TAC);;

(* Lean: left_minus *)
let C1092MNCS_LEFT_MINUS = prove
 (`forall c s h t. c977cc_normal c s /\ &252 / &373 <= s /\ c1092mcs_quarter h t /\ c * t - s * h <= &0
     ==> &0 < c1092mpbes_leftValue (&1) (c1092mncs_leftMinusA c s) (c1092mncs_leftMinusB c s) h t`,
  C1092MNCS_SETUP_TAC THEN C1092MNCS_ORDER_TAC true THEN
  SUBGOAL_THEN `h <= &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
   `--(&7 / &10) * ((t + s) / &2) <= c1092mncs_leftMinusA c s * ((t + s) / &2) /\
    c1092mncs_leftMinusB c s * ((h + c) / &2) <= --(&1 / &2) * ((h + c) / &2) /\
    (h + c) / &2 * (((h + c) / &2) / &2 - &1 / &2) <= &0 /\
    (t + s) / &2 * (&7 / &10 - (h + c) / &2 - ((t + s) / &2) / &2) <= &0`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--((h + c) / &2) * (t + s) / &2 + (((h + c) / &2) pow 2 - ((t + s) / &2) pow 2) / &2 -
    c1092mncs_leftMinusA c s * ((t + s) / &2) + c1092mncs_leftMinusB c s * ((h + c) / &2) <= &0`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092MNCS_DIFF_TAC C1092MPBES_LEFT_DIFFERENCE
    `c1092mncs_leftMinusA c s` `c1092mncs_leftMinusB c s` THEN
  SUBGOAL_THEN `&0 <= (h + c) / &2 *
     (c1092mpbes_leftValue (&1) (c1092mncs_leftMinusA c s) (c1092mncs_leftMinusB c s) h t -
      c1092mpbes_leftValue (&1) (c1092mncs_leftMinusA c s) (c1092mncs_leftMinusB c s) c s)`
    MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&0 <= (t - s) * d <=> &0 <= (s - t) * --d`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&0 < c /\ &0 <= h ==> &0 < (h + c) / &2`;
           ASSUME `&0 <= h`; REAL_ARITH `&7 / &10 < c ==> &0 < c`; ASSUME `&7 / &10 < c`] THEN
  RASM_ARITH_TAC);;
