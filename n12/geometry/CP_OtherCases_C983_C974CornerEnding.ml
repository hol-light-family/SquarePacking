(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974CornerEnding.lean          *)
(* (N12Compact.Completion.OtherCases.C983.C974CornerEnding).                 *)
(* C974-THREE-SQUARE-ENDING section 4, in the wall-origin chart.  Square W   *)
(* is cW sW uW vW aW (with C974WallReach.Data = oc983wr_data), the actual    *)
(* corner C is cC sC uC vC aC, the direction is (c, s).  Lean's              *)
(* q = (pullX C).translated 2 (-1) is the explicit square of OC983CE_CHART.  *)
(* upper / lower are ABT_upper / ABT_lower; profile is C1092WPS_profile;     *)
(* corner_profile is OCWPCP_CORNER_PROFILE; C974CornerScalars lemmas are     *)
(* C983CS_*.  Tag OC983CE_.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974WallReach.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let OC983CE_CHART = prove
 (`forall c s u v a x y.
     linside (--c) s (u - &2 * c + s) (--v - a - &2 * s - c) a x y <=>
     linside c s u v a (&2 - x) (y - &1)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let OC983CE_CANCEL = prove
 (`forall k x y. &0 < k /\ k * x = k * y ==> x = y`,
  MESON_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ]);;

let OC983CE_POS_CANCEL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < k * --y` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let OC983CE_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: corner_lower (private) *)
let OC983CE_CORNER_LOWER = prove
 (`forall cC sC uC vC aC c s.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\
     (forall x y. linside cC sC uC vC aC x y ==> x <= &2 /\ --(&1) <= y) /\
     linside cC sC uC vC aC (&1) (&0) /\ ~linside cC sC uC vC aC (&1) (&1 / &2) /\
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> ABT_lower cC sC uC vC aC c s <= &2 * c - s - aC * C1092WPS_profile c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--cC`; `sC:real`; `uC - &2 * cC + sC`; `--vC - aC - &2 * sC - cC`;
                `aC:real`; `c:real`; `s:real`] OCWPCP_CORNER_PROFILE) THEN
  REWRITE_TAC[OC983CE_CHART] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 - x`; `y - &1`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `U = &2 * c - s - L ==> A <= U ==> L <= &2 * c - s - A`) THEN
  REWRITE_TAC[ABT_upper; ABT_lower; tss_support_radius; lcx; lcy] THEN
  REWRITE_TAC[REAL_ARITH `abs(c * --cC + --s * sC) = abs(c * cC + s * sC)`;
              REAL_ARITH `abs(--c * sC + --s * --cC) = abs(--c * sC + s * cC)`] THEN
  UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING);;

(* Lean: profile_form (private) *)
let OC983CE_PROFILE_FORM = prove
 (`forall c s. &0 <= c /\ c pow 2 + s pow 2 = &1
         ==> C1092WPS_profile c s = c * (&2 - s / (&1 + c)) - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C1092WPS_profile] THEN
  SUBGOAL_THEN `&0 < &1 + c` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_FIELD);;

let OC983CE_IS_DIVEQ th =
  let t = concl th in
  is_eq t && is_var(lhand t) &&
  can (find_term (fun u -> try fst(dest_const u) = "real_div" with Failure _ -> false))
      (rand t);;

(* Lean: quadrant (private) *)
let OC983CE_QUADRANT = prove
 (`forall cW sW uW vW aW cC sC uC vC aC beta c s.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cC * cC + sC * sC = &1 /\ &0 < aC /\
     oc983wr_data cW sW uW vW aW /\ aW = aC /\
     (forall x y. linside cC sC uC vC aC x y ==> x <= &2 /\ --(&1) <= y) /\
     linside cC sC uC vC aC (&1) (&0) /\ ~linside cC sC uC vC aC (&1) (&1 / &2) /\
     &0 < beta /\ linside cW sW uW vW aW (&1) (--beta) /\
     sW / (&1 + cW) - &1 / &2 < --beta /\ sW < &1 / &2 /\ aW - sW / &2 < uW + aW /\
     &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1
     ==> ABT_lower cC sC uC vC aC c s < ABT_upper cW sW uW vW aW c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aC`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] OC983WR_FRAME_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `oc983wr_data cW sW uW vW aW` THEN REWRITE_TAC[oc983wr_data] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cW pow 2 + sW pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  (* the corner support *)
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aW:real`; `c:real`; `s:real`]
    OC983CE_CORNER_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OC983CE_PROFILE_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* strict bounds at the actual points *)
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `&1`; `--beta`; `c:real`; `s:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aW:real`;
                `&1`; `&0`; `c:real`; `s:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ASSUME `linside cW sW uW vW aW (&0) (&0)`) THEN REWRITE_TAC[linside] THEN
  STRIP_TAC THEN
  (* half-angle data of both normals *)
  MP_TAC(SPECL [`cW:real`; `sW:real`] C983CS_NORMAL_FORMS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C983CS_NORMAL_FORMS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] C1092WPS_QUARTER_DATA) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; C1092WPS_half] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if free_in `s / (&1 + c)` (concl th) then MP_TAC th
                                 else NO_TAC)) THEN
  SPEC_TAC(`s / (&1 + c)`,`w:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if free_in `sW / (&1 + cW)` (concl th) then MP_TAC th
                                 else NO_TAC)) THEN
  SPEC_TAC(`sW / (&1 + cW)`,`z:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `z:real`; `c:real`; `s:real`; `w:real`] C983CS_CUBIC_GAP) THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC(map EQT_INTRO (filter OC983CE_IS_DIVEQ ths))) THEN
  DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check OC983CE_IS_DIVEQ)) THEN
  SUBGOAL_THEN `&0 < &1 + w pow 2 /\ &0 < &1 + z pow 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `w <= z` THENL
   [(* the relative angle is not larger *)
    SUBGOAL_THEN `cW <= c` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= c - cW ==> cW <= c`) THEN
      MATCH_MP_TAC OC983CE_POS_CANCEL THEN
      EXISTS_TAC `(&1 + z pow 2) * (&1 + w pow 2)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `((&1 + z pow 2) * (&1 + w pow 2)) * (c - cW) = &2 * (z pow 2 - w pow 2)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(&1 + w pow 2) * c = &1 - w pow 2` THEN
        UNDISCH_TAC `(&1 + z pow 2) * cW = &1 - z pow 2` THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      OC983CE_PROD_TAC [`&0 <= (z - w) * (z + w)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    OC983CE_PROD_TAC [`&0 < (c - &4 / &5) * (&2 - w)`] THEN
    SUBGOAL_THEN `&0 < C1092WPS_profile c s` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    OC983CE_PROD_TAC
     [`&0 < s * (--beta - (z - &1 / &2))`;
      `&0 < (aW - &1) * C1092WPS_profile c s`] THEN
    SUBGOAL_THEN `&0 <= s * (z - w + w pow 2 / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c + s * (z - &1 / &2) - (&2 * c - s - aW * C1092WPS_profile c s) =
        (aW - &1) * C1092WPS_profile c s + s * (z - w + w pow 2 / &2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OC983CE_CANCEL THEN
      EXISTS_TAC `&1 + w pow 2` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(&1 + w pow 2) * c = &1 - w pow 2` THEN
      UNDISCH_TAC `(&1 + w pow 2) * s = &2 * w` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    (* the relative angle is larger *)
    SUBGOAL_THEN `&0 <= --c * sW + s * cW` ASSUME_TAC THENL
     [MATCH_MP_TAC OC983CE_POS_CANCEL THEN
      EXISTS_TAC `(&1 + z pow 2) * (&1 + w pow 2)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `((&1 + z pow 2) * (&1 + w pow 2)) * (--c * sW + s * cW) =
                    &2 * (w - z) * (&1 + w * z)` SUBST1_TAC THENL
       [UNDISCH_TAC `(&1 + w pow 2) * c = &1 - w pow 2` THEN
        UNDISCH_TAC `(&1 + w pow 2) * s = &2 * w` THEN
        UNDISCH_TAC `(&1 + z pow 2) * cW = &1 - z pow 2` THEN
        UNDISCH_TAC `(&1 + z pow 2) * sW = &2 * z` THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      OC983CE_PROD_TAC [`&0 <= w * z`] THEN
      OC983CE_PROD_TAC [`&0 <= (&2 * (w - z)) * (&1 + w * z)`] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    OC983CE_PROD_TAC [`&0 < c * cW`; `&0 < s * sW`] THEN
    SUBGOAL_THEN `ABT_upper cW sW uW vW aW c s =
        (c * cW + s * sW) * (uW + aW) + (--c * sW + s * cW) * (vW + aW)` ASSUME_TAC THENL
     [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
      SUBGOAL_THEN `abs(c * cW + s * sW) = c * cW + s * sW /\
                    abs(--c * sW + s * cW) = --c * sW + s * cW`
        (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    OC983CE_PROD_TAC
     [`&0 < (c * cW + s * sW) * ((uW + aW) - (aW - sW / &2))`;
      `&0 <= (--c * sW + s * cW) * (vW + aW)`] THEN
    SUBGOAL_THEN `(c * cW + s * sW) * (aW - sW / &2) < ABT_upper cW sW uW vW aW c s`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&1 / &2 <= c` THENL
     [SUBGOAL_THEN `c <= c * cW + s * sW` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
        MATCH_MP_TAC OC983CE_POS_CANCEL THEN EXISTS_TAC `cW:real` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `cW * ((c * cW + s * sW) - c) = c * (&1 - cW) + sW * (--c * sW + s * cW)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        OC983CE_PROD_TAC [`&0 <= c * (&1 - cW)`; `&0 <= sW * (--c * sW + s * cW)`] THEN
        RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `s <= &1` ASSUME_TAC THENL
       [NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
      SUBGOAL_THEN `w < &1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        OC983CE_PROD_TAC [`&0 <= (w - &1) * (&1 + c)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      OC983CE_PROD_TAC [`&0 <= (c - &1 / &2) * (&3 - w)`] THEN
      SUBGOAL_THEN `&0 < (c * cW + s * sW) + C1092WPS_profile c s` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      OC983CE_PROD_TAC [`&0 < (aW - &1) * ((c * cW + s * sW) + C1092WPS_profile c s)`] THEN
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
          rand(concl th) = `&0 < (&1 - sW / &2) * (c * cW + s * sW) - &1 + w` then
        MP_TAC th THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC]
        else NO_TAC) THEN
      RASM_ARITH_TAC;
      SUBGOAL_THEN `(&3 / &2) * c < s` ASSUME_TAC THENL
       [NLIN_TAC [SQ_NONNEG `c:real`]; ALL_TAC] THEN
      MP_TAC(SPECL [`cW:real`; `sW:real`] C983CS_STEEP_GAIN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      OC983CE_PROD_TAC [`&0 < sW * (s - (&3 / &2) * c)`] THEN
      SUBGOAL_THEN `c * (cW + (&3 / &2) * sW) < c * cW + s * sW` ASSUME_TAC THENL
       [RASM_ARITH_TAC; ALL_TAC] THEN
      OC983CE_PROD_TAC
       [`&0 < (&1 - sW / &2) * ((c * cW + s * sW) - c * (cW + (&3 / &2) * sW))`;
        `&0 < c * ((cW + (&3 / &2) * sW) * (&1 - sW / &2) - &1)`;
        `&0 < (c * cW + s * sW) * (aW - &1)`] THEN
      RASM_ARITH_TAC]]);;

(* the actual separating normals are excluded (Lean: noSeparator, local) *)
let OC983CE_NO_SEPARATOR = prove
 (`forall cW sW uW vW aW cC sC uC vC aC c s.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cC * cC + sC * sC = &1 /\ &0 < aC /\
     oc983wr_data cW sW uW vW aW /\ aW = aC /\
     (forall x y. linside cC sC uC vC aC x y ==> x <= &2 /\ --(&1) <= y) /\
     linside cC sC uC vC aC (&1) (&0) /\ ~linside cC sC uC vC aC (&1) (&1 / &2) /\
     c pow 2 + s pow 2 = &1 /\
     ABT_upper cW sW uW vW aW c s <= ABT_lower cC sC uC vC aC c s
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aC`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] OC983WR_REACH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `oc983wr_data cW sW uW vW aC`) THEN REWRITE_TAC[oc983wr_data] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `&4 / &5`; `&0`; `c:real`; `s:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `&1`; `--beta`; `c:real`; `s:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&1`; `&0`; `c:real`; `s:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= beta * --s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `beta:real`; `c:real`; `s:real`] OC983CE_QUADRANT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: impossible *)
let OC983CE_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cC sC uC vC aC.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cC * cC + sC * sC = &1 /\ &0 < aC /\
     oc983wr_data cW sW uW vW aW /\ aW = aC /\
     (forall x y. linside cC sC uC vC aC x y ==> x <= &2 /\ --(&1) <= y) /\
     linside cC sC uC vC aC (&1) (&0) /\ ~linside cC sC uC vC aC (&1) (&1 / &2) /\
     ldisj cW sW uW vW aW cC sC uC vC aC
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aC`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aW:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  let ns = [`cW:real`, `sW:real`; `--sW:real`, `cW:real`;
            `cC:real`, `sC:real`; `--sC:real`, `cC:real`] in
  let negs = map (fun (x,y) -> (mk_comb(`(--):real->real`,x), mk_comb(`(--):real->real`,y))) ns in
  FIRST (map (fun (x,y) ->
    MATCH_MP_TAC OC983CE_NO_SEPARATOR THEN
    MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                          `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aW:real`; x; y] THEN
    ASM_REWRITE_TAC[REAL_POW_2; OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC) (ns @ negs)));;
