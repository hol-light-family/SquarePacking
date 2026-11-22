(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeMixedCubic.lean        *)
(* (N12Compact.Completion.OtherCases.C983.NegativeMixedCubic).               *)
(* The mixed-angle numerator is 4w times a cubic in z-w whose coefficients   *)
(* increase on [1/9,2/7].  The Lean monotonicity-by-derivative argument is   *)
(* replaced by exact factorizations A(w)-A(1/9) = (w-1/9) Q(w), Q >= 0.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;

(* Lean: numerator *)
let occ983nmc_numerator = new_definition
 `occ983nmc_numerator (z:real) w =
    &4 * w * z * (&1 + w pow 2) * (&1 + z pow 2) -
    ((&1 - w pow 2) * (&1 - z pow 2) + &4 * w * z) * (&1 - &2 * w + &3 * w pow 2) *
      (&1 + z) +
    (&1 - z pow 2) * (&1 - w) pow 2 * (&1 + w pow 2) * (&1 + z)`;;

(* Lean: A0, A1, A2, A3, cubic (private definitions) *)
let occ983nmc_cubic = new_definition
 `occ983nmc_cubic (w:real) y =
    w pow 3 * (&1 - w) * (&1 + w pow 2) +
    w pow 2 * (&4 - &3 * w) * (&1 + w pow 2) * y +
    (--(&3) * w pow 4 + &5 * w pow 3 - &2 * w pow 2 + &5 * w - &1) * y pow 2 +
    (&1 + &2 * w pow 2 - w pow 3) * y pow 3`;;

let OCC983NMC_POWER_FACTS = prove
 (`forall w. &1 / &9 <= w /\ w <= &2 / &7
       ==> &0 <= w pow 2 /\ &0 <= w pow 3 /\ &0 <= w pow 4 /\
           w pow 2 <= &2 / &7 * w /\
           w pow 3 <= &2 / &7 * w pow 2 /\ w pow 4 <= &2 / &7 * w pow 3 /\
           w pow 5 <= &2 / &7 * w pow 4`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `w pow 2 = w * w /\ w pow 3 = w * w * w /\
                          w pow 4 = w * w * w * w /\ w pow 5 = w * w * w * w * w`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= w * w`; `w * w <= &2 / &7 * w`;
    `&0 <= w * w * w`; `w * w * w <= &2 / &7 * w * w`;
    `&0 <= w * w * w * w`; `w * w * w * w <= &2 / &7 * w * w * w`;
    `w * w * w * w * w <= &2 / &7 * w * w * w * w`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: coefficients_lower (private; via derivative_bounds and          *)
(* coefficient_monotone in Lean)                                          *)
let OCC983NMC_COEFFICIENTS_LOWER = prove
 (`forall w. &1 / &9 <= w /\ w <= &2 / &7
       ==> &656 / &531441 <= w pow 3 * (&1 - w) * (&1 + w pow 2) /\
           &902 / &19683 <= w pow 2 * (&4 - &3 * w) * (&1 + w pow 2) /\
           --(&1012 / &2187) <= --(&3) * w pow 4 + &5 * w pow 3 - &2 * w pow 2 + &5 * w - &1 /\
           &746 / &729 <= &1 + &2 * w pow 2 - w pow 3`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP OCC983NMC_POWER_FACTS) THEN
  SUBGOAL_THEN
   `&0 <= (w - &1 / &9) *
      (&656 / &59049 + &656 / &6561 * w + &656 / &729 * w pow 2 - &73 / &81 * w pow 3 +
       &8 / &9 * w pow 4 - w pow 5) /\
    &0 <= (w - &1 / &9) *
      (&902 / &2187 + &902 / &243 * w - &70 / &27 * w pow 2 + &11 / &3 * w pow 3 -
       &3 * w pow 4) /\
    &0 <= (w - &1 / &9) *
      (&1175 / &243 - &40 / &27 * w + &14 / &3 * w pow 2 - &3 * w pow 3) /\
    &0 <= (w - &1 / &9) * (&17 / &81 + &17 / &9 * w - w pow 2)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: cubic_lower (private) *)
let OCC983NMC_CUBIC_LOWER = prove
 (`forall w y. &1 / &9 <= w /\ w <= &2 / &7 /\ &0 <= y
         ==> occ983nmc_cubic (&1 / &9) y <= occ983nmc_cubic w y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `w:real` OCC983NMC_COEFFICIENTS_LOWER) THEN
  ASM_REWRITE_TAC[occ983nmc_cubic] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  SUBGOAL_THEN `&0 <= y pow 2 /\ &0 <= y pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&902 / &19683 * y <= w pow 2 * (&4 - &3 * w) * (&1 + w pow 2) * y`;
    `--(&1012 / &2187) * y pow 2 <=
     (--(&3) * w pow 4 + &5 * w pow 3 - &2 * w pow 2 + &5 * w - &1) * y pow 2`;
    `&746 / &729 * y pow 3 <= (&1 + &2 * w pow 2 - w pow 3) * y pow 3`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: left_edge (private) *)
let OCC983NMC_LEFT_EDGE = prove
 (`forall y. &0 <= y /\ y <= &11 / &63 ==> &16 / &27783 <= occ983nmc_cubic (&1 / &9) y`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = &63 / &11 * y` THEN
  SUBGOAL_THEN `&0 <= e /\ &0 <= &1 - e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y = &11 / &63 * e` SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&656 / &531441 - &16 / &27783) * (&1 - e) pow 3 +
          (&4838 / &1240029 - &16 / &27783) * (&3 * e * (&1 - e) pow 2) +
          (&200 / &107163 - &16 / &27783) * (&3 * e pow 2 * (&1 - e))`
  MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    TRY(CONV_TAC REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[occ983nmc_cubic] THEN REAL_ARITH_TAC]);;

(* Lean: triangle_margin *)
let OCC983NMC_TRIANGLE_MARGIN = prove
 (`forall z w. &1 / &9 <= w /\ w <= z /\ z <= &2 / &7
         ==> &64 / &250047 <= occ983nmc_numerator z w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `z - w` OCC983NMC_LEFT_EDGE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`w:real`; `z - w`] OCC983NMC_CUBIC_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `occ983nmc_numerator z w = &4 * w * occ983nmc_cubic w (z - w)`
    SUBST1_TAC THENL
   [REWRITE_TAC[occ983nmc_numerator; occ983nmc_cubic] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (w - &1 / &9) * occ983nmc_cubic w (z - w)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: triangle *)
let OCC983NMC_TRIANGLE = prove
 (`forall z w. &1 / &9 <= w /\ w <= z /\ z <= &2 / &7 ==> &0 <= occ983nmc_numerator z w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`z:real`; `w:real`] OCC983NMC_TRIANGLE_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
