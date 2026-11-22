(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveBoundArc.lean         *)
(* (namespace N12Compact.C1092MPPMMissingPositiveBoundaries.Arc).  The       *)
(* sine-concavity step on the upper unit-circle arc.  cosH / sinH:           *)
(* c1092sps_cosH / c1092sps_sinH; Real.sqrt is sqrt.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundProfiles.ml";;

(* Lean: polynomial (definition) *)
let c1092mpba_polynomial = new_definition
 `c1092mpba_polynomial (q:real) (z:real) (r:real) =
    (q + z + r) - (q pow 2 + z pow 2 + r pow 2) - (q * z + q * r + z * r) -
    ((q * z) pow 2 + (q * r) pow 2 + (z * r) pow 2) - q * z * r * (q + z + r) -
    q * z * r * (q * z + q * r + z * r)`;;

let C1092MPBA_LIN_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then RASM_ARITH_TAC g else NLIN_TAC ~deg2:false [] g));;

let C1092MPBA_MUL_TAC th x y =
  MP_TAC(SPECL [x; y] th) THEN ANTS_TAC THENL [C1092MPBA_LIN_TAC; DISCH_TAC];;

(* Lean: polynomial_nonneg *)
let C1092MPBA_POLYNOMIAL_NONNEG = prove
 (`forall d q z r. &0 <= d /\ d pow 2 + &2 * d = &1 /\
             &0 <= q /\ q <= d /\ &0 <= z /\ z <= d /\ &0 <= r /\ r <= d
             ==> &0 <= c1092mpba_polynomial q z r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mpba_polynomial] THEN
  ABBREV_TAC `S = q + z + r` THEN ABBREV_TAC `P = q * z + q * r + z * r` THEN
  SUBGOAL_THEN `q * z * r * S = (q * z * r) * S /\ q * z * r * P = (q * z * r) * P`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `R = q * z * r` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MAP_EVERY (fun (x,y) -> C1092MPBA_MUL_TAC REAL_LE_MUL x y)
   [`q:real`,`z:real`; `q:real`,`r:real`; `z:real`,`r:real`] THEN
  SUBGOAL_THEN `&0 <= S /\ &0 <= P /\ &0 <= R` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "P"; "R"] THEN REPEAT CONJ_TAC THENL
     [C1092MPBA_LIN_TAC; C1092MPBA_LIN_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN C1092MPBA_LIN_TAC];
    ALL_TAC] THEN
  (* q^2+z^2+r^2 <= d S *)
  MAP_EVERY (fun (x,y) -> C1092MPBA_MUL_TAC REAL_LE_MUL x y)
   [`q:real`,`d - q`; `z:real`,`d - z`; `r:real`,`d - r`;
    `q:real`,`d - z`; `z:real`,`d - q`; `q:real`,`d - r`;
    `r:real`,`d - q`; `z:real`,`d - r`; `r:real`,`d - z`] THEN
  SUBGOAL_THEN `q * q + z * z + r * r <= d * S /\ P <= d * S` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "P"] THEN C1092MPBA_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * z <= d * d /\ q * r <= d * d /\ z * r <= d * d` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN C1092MPBA_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R <= d * d * d` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    C1092MPBA_MUL_TAC REAL_LE_MUL `d * d - q * z` `r:real` THEN
    C1092MPBA_MUL_TAC REAL_LE_MUL `d * d` `d - r` THEN
    C1092MPBA_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q * z) * (q * z) + (q * r) * (q * r) + (z * r) * (z * r) <= d * d * d * S`
    ASSUME_TAC THENL
   [C1092MPBA_MUL_TAC REAL_LE_MUL `d * d - q * z` `q * z` THEN
    C1092MPBA_MUL_TAC REAL_LE_MUL `d * d - q * r` `q * r` THEN
    C1092MPBA_MUL_TAC REAL_LE_MUL `d * d - z * r` `z * r` THEN
    C1092MPBA_MUL_TAC REAL_LE_MUL `d * d` `d * S - (q * z + q * r + z * r)` THEN
    C1092MPBA_LIN_TAC;
    ALL_TAC] THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `d * d * d - R` `S:real` THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `d * d * d - R` `P:real` THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `d * d * d` `d * S - P` THEN
  SUBGOAL_THEN `(&1 - &2 * d - &2 * d * d * d - d * d * d * d) * S = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - &2 * d - &2 * d * d * d - d * d * d * d =
                  (&1 + d * d) * (&1 - &2 * d - d * d)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 - &2 * d - d * d = &0` SUBST1_TAC THENL
     [C1092MPBA_LIN_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  C1092MPBA_LIN_TAC);;

(* Lean: value (definition) *)
let c1092mpba_value = new_definition
 `c1092mpba_value (a:real) (A:real) (B:real) (z:real) =
    (a / &2) * (&1 + c1092sps_cosH z pow 2 + c1092sps_sinH z * c1092sps_cosH z) +
    A * c1092sps_sinH z + B * c1092sps_cosH z`;;

(* the exact chord identity of nonneg, with the weights alpha / beta *)
let C1092MPBA_CHORD_IDENTITY = prove
 (`forall a A B q z r.
     ~(r - q = &0) /\ ~(&1 + r * q = &0)
     ==> ((&1 + q * r) * (&1 + z pow 2) pow 2 * (&1 + q pow 2) * (&1 + r pow 2)) *
         (c1092mpba_value a A B z -
          (((r - z) * (&1 + r * z) * (&1 + q pow 2)) /
           ((r - q) * (&1 + r * q) * (&1 + z pow 2))) * c1092mpba_value a A B q -
          (((z - q) * (&1 + z * q) * (&1 + r pow 2)) /
           ((r - q) * (&1 + r * q) * (&1 + z pow 2))) * c1092mpba_value a A B r) =
         &2 * a * (z - q) * (r - z) * c1092mpba_polynomial q z r`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092mpba_value; c1092mpba_polynomial; c1092sps_cosH; c1092sps_sinH] THEN
  MAP_EVERY (fun v -> MP_TAC(SPEC v C1092SPS_HALF_DEN_NZ)) [`q:real`; `z:real`; `r:real`] THEN
  CONV_TAC REAL_FIELD);;

(* Lean: nonneg *)
let C1092MPBA_NONNEG = prove
 (`forall d a A B q z r.
     &0 <= d /\ d pow 2 + &2 * d = &1 /\ &0 <= a /\
     &0 <= q /\ q <= z /\ z <= r /\ r <= d /\
     &0 <= c1092mpba_value a A B q /\ &0 <= c1092mpba_value a A B r
     ==> &0 <= c1092mpba_value a A B z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `q:real = r` THENL
   [SUBGOAL_THEN `z:real = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `q:real`; `z:real`; `r:real`] C1092MPBA_POLYNOMIAL_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MAP_EVERY (fun v -> MP_TAC(SPEC v C1092SPS_HALF_DEN_POS) THEN DISCH_TAC)
    [`q:real`; `z:real`; `r:real`] THEN
  SUBGOAL_THEN `&0 < &1 + r * q /\ &0 < r - q` STRIP_ASSUME_TAC THENL
   [C1092MPBA_MUL_TAC REAL_LE_MUL `r:real` `q:real` THEN C1092MPBA_LIN_TAC; ALL_TAC] THEN
  ABBREV_TAC `D = (r - q) * (&1 + r * q) * (&1 + z pow 2)` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `al = ((r - z) * (&1 + r * z) * (&1 + q pow 2)) / D` THEN
  ABBREV_TAC `be = ((z - q) * (&1 + z * q) * (&1 + r pow 2)) / D` THEN
  SUBGOAL_THEN `&0 <= al /\ &0 <= be` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["al"; "be"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN TRY C1092MPBA_LIN_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC) THEN
    TRY C1092MPBA_LIN_TAC THEN
    MP_TAC(SPECL [`r:real`; `z:real`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`z:real`; `q:real`] REAL_LE_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092MPBA_LIN_TAC; DISCH_TAC]) THEN C1092MPBA_LIN_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K = (&1 + q * r) * (&1 + z pow 2) pow 2 * (&1 + q pow 2) * (&1 + r pow 2)` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MP_TAC(SPECL [`q:real`; `r:real`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MPBA_LIN_TAC; DISCH_TAC] THEN C1092MPBA_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `K * (c1092mpba_value a A B z - al * c1092mpba_value a A B q - be * c1092mpba_value a A B r) =
    &2 * a * (z - q) * (r - z) * c1092mpba_polynomial q z r` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "al"; "be"; "D"] THEN
    MATCH_MP_TAC C1092MPBA_CHORD_IDENTITY THEN C1092MPBA_LIN_TAC ORELSE
    (CONJ_TAC THEN ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `a:real` `z - q` THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `r - z` `c1092mpba_polynomial q z r` THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `a * (z - q)` `(r - z) * c1092mpba_polynomial q z r` THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `al:real` `c1092mpba_value a A B q` THEN
  C1092MPBA_MUL_TAC REAL_LE_MUL `be:real` `c1092mpba_value a A B r` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`K:real`;
    `--(c1092mpba_value a A B z - al * c1092mpba_value a A B q - be * c1092mpba_value a A B r)`]
    REAL_LT_MUL) THEN
  ANTS_TAC THENL [C1092MPBA_LIN_TAC; DISCH_TAC] THEN
  C1092MPBA_LIN_TAC);;

(* Lean: diagonal (definition) *)
let c1092mpba_diagonal = new_definition `c1092mpba_diagonal = sqrt(&2) - &1`;;

(* Lean: diagonal_data *)
let C1092MPBA_DIAGONAL_DATA = prove
 (`&0 < c1092mpba_diagonal /\ c1092mpba_diagonal < &1 / &2 /\
   c1092mpba_diagonal pow 2 + &2 * c1092mpba_diagonal = &1 /\
   c1092sps_cosH c1092mpba_diagonal = sqrt(&2) / &2 /\
   c1092sps_sinH c1092mpba_diagonal = sqrt(&2) / &2`,
  REWRITE_TAC[c1092mpba_diagonal; c1092sps_cosH; c1092sps_sinH] THEN
  MP_TAC(SPEC `&2` SQRT_POW_2) THEN MP_TAC(SPEC `&2` SQRT_POS_LT) THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &2 /\ &0 < &2`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SPEC_TAC(`sqrt(&2)`,`w:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&7 / &5 < w /\ w < &3 / &2` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + (w - &1) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `w - &1` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  UNDISCH_TAC `w pow 2 = &2` THEN CONV_TAC REAL_RING);;
