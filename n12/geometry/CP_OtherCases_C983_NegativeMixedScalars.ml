(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeMixedScalars.lean      *)
(* (N12Compact.Completion.OtherCases.C983.NegativeMixedScalars).  The       *)
(* remaining mixed separator scalar: half-angle substitution z = half c t,   *)
(* w = half a b (C1092WPS_half / C1092WPS_QUARTER_DATA), the numerator of   *)
(* NegativeMixedCubic (occ983nmc_numerator, which is the Lean private        *)
(* `numerator` verbatim) and its margin 64/250047.  The Lean field_simp     *)
(* identity is proved by REAL_RING from the half-angle equations.            *)
(* Tag C983NMSC_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeMixedShallow.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeMixedCubic.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: triangle (private; numerator = NegativeMixedCubic.numerator) *)
let C983NMSC_TRIANGLE = prove
 (`forall z w. &1 / &9 <= w /\ w <= z /\ z <= &2 / &7 ==> &0 <= occ983nmc_numerator z w`,
  REWRITE_TAC[OCC983NMC_TRIANGLE]);;

(* Lean: large_margin *)
let C983NMSC_LARGE_MARGIN = prove
 (`forall c t a b. &0 < c /\ &0 < t /\ &0 < a /\ &0 <= b /\
     c pow 2 + t pow 2 = &1 /\ a pow 2 + b pow 2 = &1 /\
     &6 / &7 < c /\ &9 / &41 <= b /\ b * c <= a * t
     ==> &153664 / &976781997 <=
         c * (&1 - b) + b * (&1 - (&1 - t) / c) - (a * c + b * t) * (&2 - a - b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`C1092WPS_half a b`, `w:real`) THEN
  SPEC_TAC(`C1092WPS_half c t`, `z:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = &1 - (&1 - t) / c` THEN
  SUBGOAL_THEN `c * h = c - (&1 - t)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z pow 2 /\ &0 <= w pow 2 /\ &0 <= z * w` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* zSmall *)
  SUBGOAL_THEN `z <= &2 / &7` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&4 / &49 < z pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 + z pow 2) * (c - &6 / &7)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_LDISTRIB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* aSmall, wLarge *)
  SUBGOAL_THEN `a <= &40 / &41` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&81 / &1681 <= b * b /\ &1600 / &1681 < a * a` MP_TAC THENL
     [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &9 <= w` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (w - &1 / &9) * (&1 + a)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_SUB_RDISTRIB] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= w - &1 / &9 ==> &1 / &9 <= w`) THEN
      MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `&1 + a` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* crossIdentity, wz *)
  SUBGOAL_THEN `(&1 + z pow 2) * (&1 + w pow 2) * (a * t - b * c) =
                &2 * (z - w) * (&1 + z * w)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_RING
     `(&1 + w pow 2) * a = &1 - w pow 2 /\ (&1 + w pow 2) * b = &2 * w /\
      (&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * t = &2 * z
      ==> (&1 + z pow 2) * (&1 + w pow 2) * (a * t - b * c) =
          &2 * (z - w) * (&1 + z * w)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w <= z` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 + z pow 2) * (&1 + w pow 2) * (a * t - b * c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (w - z) * (&1 + z * w)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* height: h * (1 + z) = 2 z *)
  SUBGOAL_THEN `h * (&1 + z) = &2 * z` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c * (&1 + z pow 2)) * (h * (&1 + z) - &2 * z) = &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_RING
       `c * h = c - (&1 - t) /\ (&1 + z pow 2) * c = &1 - z pow 2 /\
        (&1 + z pow 2) * t = &2 * z
        ==> (c * (&1 + z pow 2)) * (h * (&1 + z) - &2 * z) = &0`) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* identity *)
  SUBGOAL_THEN
   `((&1 + w pow 2) pow 2 * (&1 + z pow 2) * (&1 + z)) *
    (c * (&1 - b) + b * h - (a * c + b * t) * (&2 - a - b)) = occ983nmc_numerator z w`
  ASSUME_TAC THENL
   [REWRITE_TAC[occ983nmc_numerator] THEN
    MATCH_MP_TAC(REAL_RING
     `(&1 + w pow 2) * a = &1 - w pow 2 /\ (&1 + w pow 2) * b = &2 * w /\
      (&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * t = &2 * z /\
      h * (&1 + z) = &2 * z
      ==> ((&1 + w pow 2) pow 2 * (&1 + z pow 2) * (&1 + z)) *
          (c * (&1 - b) + b * h - (a * c + b * t) * (&2 - a - b)) =
          &4 * w * z * (&1 + w pow 2) * (&1 + z pow 2) -
          ((&1 - w pow 2) * (&1 - z pow 2) + &4 * w * z) * (&1 - &2 * w + &3 * w pow 2) *
            (&1 + z) +
          (&1 - z pow 2) * (&1 - w) pow 2 * (&1 + w pow 2) * (&1 + z)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`z:real`; `w:real`] OCC983NMC_TRIANGLE_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* denominator bounds *)
  SUBGOAL_THEN `z pow 2 <= &4 / &49 /\ w pow 2 <= &4 / &49` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  ABBREV_TAC `D = (&1 + w pow 2) pow 2 * (&1 + z pow 2) * (&1 + z)` THEN
  SUBGOAL_THEN `&0 < D /\ D <= (&53 / &49) pow 3 * (&9 / &7)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `(x:real) pow 3 * y = x pow 2 * x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `E = c * (&1 - b) + b * h - (a * c + b * t) * (&2 - a - b)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `D * E < &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E * ((&53 / &49) pow 3 * (&9 / &7) - D)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  UNDISCH_TAC `D * E = occ983nmc_numerator z w` THEN
  UNDISCH_TAC `&64 / &250047 <= occ983nmc_numerator z w` THEN
  REAL_ARITH_TAC);;

(* Lean: large *)
let C983NMSC_LARGE = prove
 (`forall c t a b. &0 < c /\ &0 < t /\ &0 < a /\ &0 <= b /\
     c pow 2 + t pow 2 = &1 /\ a pow 2 + b pow 2 = &1 /\
     &6 / &7 < c /\ &9 / &41 <= b /\ b * c <= a * t
     ==> &0 <= c * (&1 - b) + b * (&1 - (&1 - t) / c) - (a * c + b * t) * (&2 - a - b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C983NMSC_LARGE_MARGIN) THEN REAL_ARITH_TAC);;
