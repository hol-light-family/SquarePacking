(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalBottomScalars.lean        *)
(* (namespace N12Compact.C1092MPPMInwardFinal.BottomAngle).                  *)
(* INWARD-BOTTOM-ANGLE scalar comparisons on the whole canonical arcs.       *)
(* Normal: c977cc_normal; half / quarter_data: C1092WPS_half /               *)
(* C1092WPS_QUARTER_DATA; normal_bounds: C977CC_NORMAL_BOUNDS;               *)
(* canonical_half_bounds: C1092IFAS_CANONICAL_HALF_BOUNDS.  Real.sqrt 5 is   *)
(* sqrt(&5).  Tag C1092IFBS_.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalOuterOwnedScalars.ml";;

let C1092IFBS_PROD = C1092MIFS_PROD_TAC;;

(* x > 0 or x >= 0 from (1 + z^2) * x > 0 / >= 0 *)
let C1092IFBS_DIVIDE_TAC prod (asl, w as g) =
  ((if is_binop `(<=):real->real->bool` w then ONCE_REWRITE_TAC[GSYM REAL_NOT_LT]
    else ONCE_REWRITE_TAC[GSYM REAL_NOT_LE]) THEN DISCH_TAC THEN
   C1092IFBS_PROD [prod] THEN RASM_ARITH_TAC) g;;

(* the relative-unit ring step, after L and e are abbreviated *)
let C1092IFBS_UNIT_RING_TAC edef =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && rhs(concl th) = `&1` &&
    can (find_term (fun t -> t = `L:real` || t = `c * h + s * k`)) (lhs(concl th)))) THEN
  UNDISCH_TAC edef THEN UNDISCH_TAC `c * h + s * k = L` THEN CONV_TAC REAL_RING;;

(* Lean: half_identity *)
let C1092IFBS_HALF_IDENTITY = prove
 (`forall c s. c977cc_normal c s ==> &1 - c = s * C1092WPS_half c s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  SUBGOAL_THEN `(&1 + c) * (c - &1 + s * z) = &0` MP_TAC THENL
   [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: bad_arc *)
let C1092IFBS_BAD_ARC = prove
 (`forall c s. c977cc_normal c s /\
         C1092WPS_half c s pow 2 - &2 * C1092WPS_half c s + &1 / &5 <= &0
     ==> C1092WPS_half c s <= &1 - c + (&2 / &5) * s /\
         &0 <= c + s - &1 - c * s + (&2 / &5) * s pow 2 /\ &543 / &500 < c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFAS_CANONICAL_HALF_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFBS_HALF_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C1092MIFS_NORMAL_TAC THEN C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (&1 - c + (&2 / &5) * s - z) = --z * (z pow 2 - &2 * z + &1 / &5)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= z * --(z pow 2 - &2 * z + &1 / &5)`] THEN
  SUBGOAL_THEN `&0 <= &1 - c + (&2 / &5) * s - z` ASSUME_TAC THENL
   [C1092IFBS_DIVIDE_TAC `&0 < (&1 + z pow 2) * --(&1 - c + (&2 / &5) * s - z)`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &10 < z` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092IFBS_PROD [`&0 <= (&1 / &10 - z) * (&2 - z - &1 / &10)`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= z * (&5 / &12 - z)`] THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (c + s - &543 / &500) = &2 * z - &43 / &500 - (&1043 / &500) * z pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [RASM_ARITH_TAC;
    SUBGOAL_THEN `c + s - &1 - c * s + (&2 / &5) * s pow 2 = s * (&1 - c + (&2 / &5) * s - z)`
      SUBST1_TAC THENL
     [UNDISCH_TAC `&1 - c = s * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    C1092IFBS_DIVIDE_TAC `&0 <= (&1 + z pow 2) * --(c + s - &543 / &500)`]);;

(* Lean: dot_le_one *)
let C1092IFBS_DOT_LE_ONE = prove
 (`forall c s P Q. c977cc_normal c s /\ P pow 2 + Q pow 2 <= &1 ==> P * c + Q * s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P * c + Q * s) pow 2 + (P * s - Q * c) pow 2 = P pow 2 + Q pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `P * s - Q * c` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `P * c + Q * s - &1` REAL_LE_POW_2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  REPEAT DISCH_TAC THEN RASM_ARITH_TAC);;

(* Lean: positive_central_norm *)
let C1092IFBS_POSITIVE_CENTRAL_NORM = prove
 (`forall h k. c977cc_normal h k
     ==> (&1 + (&43 / &500) * k pow 2 - (&13 / &50) * h * k) pow 2 +
         ((&43 / &500) * h * k + (&13 / &50) * k pow 2) pow 2 <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `(&1 + (&43 / &500) * k pow 2 - (&13 / &50) * h * k) pow 2 +
                ((&43 / &500) * h * k + (&13 / &50) * k pow 2) pow 2 =
                &1 + (&61749 / &250000) * k pow 2 - (&13 / &25) * h * k` SUBST1_TAC THENL
   [UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= k * (h - k)`] THEN
  MP_TAC(SPEC `k:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC);;

(* Lean: positive_u_margin *)
let C1092IFBS_POSITIVE_U_MARGIN = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k /\ &543 / &500 < c + s
     ==> &0 < h * (c pow 2 / &2 + s) + k * (c - c * s / &2 - &543 / &500)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092IFBS_PROD [`&0 <= c * (c - s)`] THEN
  ABBREV_TAC `P = c pow 2 / &2 + s` THEN
  ABBREV_TAC `Q = c - c * s / &2 - &543 / &500` THEN
  SUBGOAL_THEN `&0 < P /\ &0 < P + Q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN REWRITE_TAC[REAL_POW_2] THEN
    CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= (h - k) * P`] THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    C1092IFBS_PROD [`&0 < h * P`] THEN ASM_REWRITE_TAC[];
    C1092IFBS_PROD [`&0 < k * (P + Q)`] THEN RASM_ARITH_TAC]);;

(* Lean: positive_wall_margin *)
let C1092IFBS_POSITIVE_WALL_MARGIN = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k /\
             &0 <= c + s - &1 - c * s + (&2 / &5) * s pow 2
     ==> &0 <= &1 / &2 + h pow 2 / &2 + h * k / &2 +
               h * (c + s - c * s + (&2 / &5) * s pow 2 - &2) +
               k * (c - s - c pow 2 + (&2 / &5) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `c * s <= &1 / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `c - s:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= (c - &7 / &10) * (&13 / &10 - c)`] THEN
  ABBREV_TAC `A = c + s - c * s + (&2 / &5) * s pow 2` THEN
  ABBREV_TAC `B = c - s - c pow 2 + (&2 / &5) * c * s` THEN
  SUBGOAL_THEN `&1 <= A` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&61 / &100 <= A + B` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= (h - k) * (A - &1)`; `&0 <= k * (A + B - &61 / &100)`] THEN
  SUBGOAL_THEN `&0 <= (&1 - h) pow 2 / &2 + k * (h / &2 - &39 / &100)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= h / &2 - &39 / &100` THENL
     [C1092IFBS_PROD [`&0 <= k * (h / &2 - &39 / &100)`] THEN
      MP_TAC(SPEC `&1 - h` REAL_LE_POW_2) THEN RASM_ARITH_TAC;
      C1092IFBS_PROD [`&0 <= (h - k) * (&39 / &100 - h / &2)`] THEN
      MP_TAC(SPEC `h - &139 / &200` REAL_LE_POW_2) THEN
      REWRITE_TAC[REAL_POW_2] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
      RASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 + h pow 2 / &2 + h * k / &2 + h * (A - &2) + k * B =
                (h - k) * (A - &1) + k * (A + B - &61 / &100) + (&1 - h) pow 2 / &2 +
                k * (h / &2 - &39 / &100)` ASSUME_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c + s - c * s + (&2 / &5) * s pow 2 - &2 = A - &2` SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_height *)
let C1092IFBS_NEGATIVE_HEIGHT = prove
 (`forall h k a D. c977cc_normal h k /\ &1 < a /\ --(&543 / &500) * h < D /\
             a * h + (&543 / &500) * k pow 2 - &2 <= h * D
     ==> --(&1) < D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  ASM_CASES_TAC `h <= &10 / &11` THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= (&1 - h) * ((&543 / &500) * (&1 + h) - &2)`;
                  `&0 < h * (a - &1)`] THEN
  SUBGOAL_THEN `&0 < h * (D + &1)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092IFBS_PROD [`&0 <= h * --(D + &1)`] THEN RASM_ARITH_TAC);;

(* Lean: relative_unit *)
let C1092IFBS_RELATIVE_UNIT = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k
     ==> (c * h + s * k) pow 2 + (c * k - s * h) pow 2 = &1`,
  REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN
  CONV_TAC REAL_RING);;

(* Lean: relative_dot_lower *)
let C1092IFBS_RELATIVE_DOT_LOWER = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k /\ s * h <= c * k
     ==> h <= c * h + s * k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFBS_HALF_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MIFS_NORMAL_TAC THEN C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  C1092IFBS_PROD [`&0 <= h * z`] THEN
  SUBGOAL_THEN `c * (k - h * z) = (c * k - s * h) + h * z` ASSUME_TAC THENL
   [UNDISCH_TAC `z * (&1 + c) = s` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k - h * z` ASSUME_TAC THENL
   [C1092IFBS_DIVIDE_TAC `&0 < c * --(k - h * z)`; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= s * (k - h * z)`] THEN
  SUBGOAL_THEN `c * h + s * k - h = s * (k - h * z)` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 - c = s * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_before_margin *)
let C1092IFBS_NEGATIVE_BEFORE_MARGIN = prove
 (`forall c s h k Q. c977cc_normal c s /\ c977cc_normal h k /\ c * k <= s * h /\
               C1092WPS_half c s <= Q
     ==> &1 <= c * h + s * k + Q * (s * h - c * k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `k:real`; `c:real`; `s:real`] C1092IFBS_RELATIVE_DOT_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `k:real`] C1092IFBS_RELATIVE_UNIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092MIFS_NORMAL_TAC THEN C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  C1092IFBS_PROD [`&0 <= s * (&1 - h)`; `&0 <= c * k`] THEN
  ABBREV_TAC `L = c * h + s * k` THEN
  ABBREV_TAC `e = s * h - c * k` THEN
  SUBGOAL_THEN `&0 <= e /\ e <= s` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= L` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= z * (L - c)`] THEN
  SUBGOAL_THEN `&0 <= z * (&1 + L) - e` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(L + z * e - &1) * (&1 + L) = e * (z * (&1 + L) - e)` ASSUME_TAC THENL
   [C1092IFBS_UNIT_RING_TAC `s * h - c * k = e`; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= e * (z * (&1 + L) - e)`] THEN
  SUBGOAL_THEN `&0 <= L + z * e - &1` ASSUME_TAC THENL
   [C1092IFBS_DIVIDE_TAC `&0 < (&1 + L) * --(L + z * e - &1)`; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= (Q - z) * e`] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_after_margin *)
let C1092IFBS_NEGATIVE_AFTER_MARGIN = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k /\ s * h <= c * k
     ==> &1 <= c * h + s * k + (c / &2) * (c * k - s * h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `k:real`] C1092IFBS_RELATIVE_DOT_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `k:real`] C1092IFBS_RELATIVE_UNIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  C1092IFBS_PROD [`&0 <= (h - k) * (h + k)`] THEN
  SUBGOAL_THEN `k < &71 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092IFBS_PROD [`&0 <= (k - &71 / &100) * (k + &71 / &100)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= s * h`] THEN
  ABBREV_TAC `L = c * h + s * k` THEN
  ABBREV_TAC `e = c * k - s * h` THEN
  SUBGOAL_THEN `&0 <= e /\ e <= c * k` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= c * (&1 + L - &2 * k)`] THEN
  SUBGOAL_THEN `&0 <= (c / &2) * (&1 + L) - e` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(L + (c / &2) * e - &1) * (&1 + L) = e * ((c / &2) * (&1 + L) - e)` ASSUME_TAC THENL
   [C1092IFBS_UNIT_RING_TAC `c * k - s * h = e`; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= e * ((c / &2) * (&1 + L) - e)`] THEN
  SUBGOAL_THEN `&0 <= L + (c / &2) * e - &1` ASSUME_TAC THENL
   [C1092IFBS_DIVIDE_TAC `&0 < (&1 + L) * --(L + (c / &2) * e - &1)`; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_central_norm *)
let C1092IFBS_NEGATIVE_CENTRAL_NORM = prove
 (`forall h k. c977cc_normal h k /\ (&14 / &25) * h <= k
     ==> (&1 + (&43 / &500) * h pow 2 - (&14 / &25) * h * k) pow 2 +
         ((&14 / &25) * h pow 2 + (&43 / &500) * h * k) pow 2 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `(&1 + (&43 / &500) * h pow 2 - (&14 / &25) * h * k) pow 2 +
                ((&14 / &25) * h pow 2 + (&43 / &500) * h * k) pow 2 =
                &1 + (&123249 / &250000) * h pow 2 - (&28 / &25) * h * k` SUBST1_TAC THENL
   [UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092IFBS_PROD [`&0 <= h * (k - (&14 / &25) * h)`; `&0 < h * h`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  RASM_ARITH_TAC);;

(* Lean: threshold *)
let C1092IFBS_THRESHOLD = prove
 (`forall c s. c977cc_normal c s /\
         &0 < C1092WPS_half c s pow 2 - &2 * C1092WPS_half c s + &1 / &5
     ==> C1092WPS_half c s < &1 - &2 * sqrt(&5) / &5 /\ C1092WPS_half c s < &53 / &500`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFAS_CANONICAL_HALF_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&5) /\ sqrt(&5) pow 2 = &5` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_POS; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  ABBREV_TAC `z = C1092WPS_half c s` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&2 * sqrt(&5) / &5 - (&1 - z)) * (&2 * sqrt(&5) / &5 + (&1 - z))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (z - &53 / &500) * --(z + &53 / &500 - &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC]);;
