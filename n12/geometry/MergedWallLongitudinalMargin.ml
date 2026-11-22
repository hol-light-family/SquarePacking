(* ========================================================================= *)
(* Port of Compact/Geometry/MergedWallLongitudinalMargin.lean                *)
(* (N12Compact.MergedWallLongitudinalMargin).  Final longitudinal scalar for *)
(* an escaping merged central pair.  Purely scalar.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: leftPoly, rightPoly, markerNumerator, wallNumerator (private defs) *)
let mwlm_leftpoly = new_definition
 `mwlm_leftpoly (z:real) =
    --(&43 / &500) - &7 / &10 * z - &193 / &250 * z pow 2 + &7 / &10 * z pow 3 -
    &1043 / &500 * z pow 4`;;

let mwlm_rightpoly = new_definition
 `mwlm_rightpoly (z:real) =
    &7 / &20 + &13 / &10 * z - &7 / &10 * z pow 2 + &27 / &10 * z pow 3 +
    &7 / &20 * z pow 4`;;

let mwlm_marker = new_definition
 `mwlm_marker (r:real) t z = r * mwlm_leftpoly z + t * mwlm_rightpoly z`;;

let mwlm_wall = new_definition
 `mwlm_wall (r:real) t z = r * mwlm_marker r t z + (r - &457 / &500) * (&1 + z pow 2) pow 2`;;

let MWLM_DEFS = [mwlm_wall; mwlm_marker; mwlm_leftpoly; mwlm_rightpoly];;

(* Lean: small_cosine (private) *)
let MWLM_SMALL_COSINE = prove
 (`forall r t z. &0 < r /\ &0 <= t /\ r pow 2 + t pow 2 = &1 /\ r <= &457 / &500 /\
           &0 <= z /\ z <= &1 / &5 ==> &0 <= mwlm_marker r t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&11 / &25 * r <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (&11 / &25 * r - t) * (&11 / &25 * r + t)`;
      `&0 <= (&457 / &500 - r) * (&457 / &500 + r)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mwlm_rightpoly z` ASSUME_TAC THENL
   [REWRITE_TAC[mwlm_rightpoly] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `z:real`]
     [`&0 <= z * (&13 / &10 - &7 / &10 * z)`; `&0 <= z * z pow 2`;
      `&0 <= z pow 4`] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`;
                REAL_ARITH `z pow 4 = (z * z) * (z * z)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`;
                REAL_ARITH `z pow 4 = (z * z) * (z * z)`]) THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mwlm_leftpoly z + &11 / &25 * mwlm_rightpoly z` ASSUME_TAC THENL
   [SUBGOAL_THEN `mwlm_leftpoly z + &11 / &25 * mwlm_rightpoly z =
       &17 / &250 * (&1 - &5 * z) pow 4 +
       &4 * &77 / &1250 * (&5 * z) * (&1 - &5 * z) pow 3 +
       &6 * &6 / &125 * (&5 * z) pow 2 * (&1 - &5 * z) pow 2 +
       &4 * &484 / &15625 * (&5 * z) pow 3 * (&1 - &5 * z) +
       &876 / &78125 * (&5 * z) pow 4` SUBST1_TAC THENL
     [REWRITE_TAC[mwlm_leftpoly; mwlm_rightpoly] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &5 * z /\ &0 <= &1 - &5 * z` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mwlm_marker] THEN
  NLIN_FACTS_TAC []
   [`&0 <= r * (mwlm_leftpoly z + &11 / &25 * mwlm_rightpoly z)`;
    `&0 <= (t - &11 / &25 * r) * mwlm_rightpoly z`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: quartic_chord (private) *)
let MWLM_QUARTIC_CHORD = prove
 (`forall a0 a1 a2 a3 a4 z Z.
      &0 <= z /\ z <= Z /\ &0 < Z /\ Z <= &1 / &5 /\
      &0 <= a3 /\ a4 <= &0 /\ a2 + &2 / &5 * a3 <= &0 /\
      &0 <= a0 /\ &0 <= a0 + a1 * Z + a2 * Z pow 2 + a3 * Z pow 3 + a4 * Z pow 4
      ==> &0 <= a0 + a1 * z + a2 * z pow 2 + a3 * z pow 3 + a4 * z pow 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= z pow 2 + z * Z + Z pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL) THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a2 + a3 * (z + Z) + a4 * (z pow 2 + z * Z + Z pow 2) <= &0`
    ASSUME_TAC THENL
   [NLIN_FACTS_TAC []
     [`&0 <= a3 * (&2 / &5 - (z + Z))`;
      `a4 * (z pow 2 + z * Z + Z pow 2) <= &0`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (Z - z) * a0 /\
    &0 <= z * (a0 + a1 * Z + a2 * Z pow 2 + a3 * Z pow 3 + a4 * Z pow 4) /\
    &0 <= (Z * (z * (Z - z))) *
          --(a2 + a3 * (z + Z) + a4 * (z pow 2 + z * Z + Z pow 2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Z * (a0 + a1 * z + a2 * z pow 2 + a3 * z pow 3 + a4 * z pow 4) =
    (Z - z) * a0 + z * (a0 + a1 * Z + a2 * Z pow 2 + a3 * Z pow 3 + a4 * Z pow 4) +
    (Z * (z * (Z - z))) * --(a2 + a3 * (z + Z) + a4 * (z pow 2 + z * Z + Z pow 2))`
  ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `Z:real` THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_REAL_ARITH_TAC);;

let MWLM_ZPOW = prove
 (`(&0:real) pow 2 = &0 /\ (&0:real) pow 3 = &0 /\ (&0:real) pow 4 = &0`,
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: large_cosine (private) *)
let MWLM_LARGE_COSINE = prove
 (`forall r t z. &0 < r /\ &0 <= t /\ r pow 2 + t pow 2 = &1 /\ &457 / &500 <= r /\
           &0 <= z /\ r * t * z < &1 - r - &43 / &500 * t pow 2
           ==> &0 <= mwlm_wall r t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`] [`r <= &1`] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO;
      REAL_ADD_RID; REAL_SUB_RZERO]) THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `t <= &9 / &20 * r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (t - &9 / &20 * r) * (t + &9 / &20 * r)`;
      `&0 <= (r - &457 / &500) * (r + &457 / &500)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Z = (&1 - r - &43 / &500 * t pow 2) / (r * t)` THEN
  SUBGOAL_THEN `r * t * Z = &1 - r - &43 / &500 * t pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z < Z` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC `r * t` THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_ASSOC]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * (&1 + r) * Z = t * (&457 / &500 - &43 / &500 * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `r * t * Z = &1 - r - &43 / &500 * t pow 2` THEN
    UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * ((&11 / &25) * (&1 + r) - (&457 / &500 - &43 / &500 * r))`;
    `&0 <= ((&11 / &25) * (&1 + r)) * (&9 / &20 * r - t)`;
    `&0 < r * (&1 + r)`;
    `Z <= &99 / &500`;
    `&0 <= t * (r - (&457 / &500 - &43 / &500 * r))`;
    `(&1 + r) * Z <= t`] THEN
  SUBGOAL_THEN `Z <= &1 / &5` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * (&1 - Z pow 2) - &2 * r * Z` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + r) * (t * (&1 - Z pow 2) - &2 * r * Z) =
                  (t - (&1 + r) * Z) * (&1 + r + t * Z)` ASSUME_TAC THENL
     [UNDISCH_TAC `r * (&1 + r) * Z = t * (&457 / &500 - &43 / &500 * r)` THEN
      UNDISCH_TAC `r * t * Z = &1 - r - &43 / &500 * t pow 2` THEN
      UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= t * Z`;
      `&0 <= (t - (&1 + r) * Z) * (&1 + r + t * Z)`] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `&1 + r` THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Z * (&1 + Z pow 2) + &7 / &20 * (&1 - &2 * Z - Z pow 2)`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Z * Z pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= Z * (&1 / &5 - Z)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mwlm_wall r t Z` ASSUME_TAC THENL
   [SUBGOAL_THEN `mwlm_wall r t Z =
       r * (t * (&1 - Z pow 2) - &2 * r * Z) *
       (Z * (&1 + Z pow 2) + &7 / &20 * (&1 - &2 * Z - Z pow 2))` SUBST1_TAC THENL
     [REWRITE_TAC MWLM_DEFS THEN
      UNDISCH_TAC `r * t * Z = &1 - r - &43 / &500 * t pow 2` THEN
      UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mwlm_wall r t (&0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `mwlm_wall r t (&0) = (r * t) * (&7 / &20 - Z)` SUBST1_TAC THENL
     [REWRITE_TAC MWLM_DEFS THEN
      UNDISCH_TAC `r * t * Z = &1 - r - &43 / &500 * t pow 2` THEN
      UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall x. mwlm_wall r t x =
        (--(&43 / &500) * r pow 2 + &7 / &20 * r * t + r - &457 / &500) +
        (--(&7 / &10) * r pow 2 + &13 / &10 * r * t) * x +
        (--(&193 / &250) * r pow 2 - &7 / &10 * r * t + &2 * r - &457 / &250) * x pow 2 +
        (&7 / &10 * r pow 2 + &27 / &10 * r * t) * x pow 3 +
        (--(&1043 / &500) * r pow 2 + &7 / &20 * r * t + r - &457 / &500) * x pow 4`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC MWLM_DEFS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MWLM_ZPOW; REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID]) THEN
  SUBGOAL_THEN `r * t <= r pow 2 / &2` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= r * (&9 / &20 * r - t)`] THEN
    REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &7 / &10 * r pow 2 + &27 / &10 * r * t` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= r * t`; `&0 <= r pow 2`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1043 / &500) * r pow 2 + &7 / &20 * r * t + r - &457 / &500 <= &0`
    ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= (r - &457 / &500) * (r + &457 / &500)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `(--(&193 / &250) * r pow 2 - &7 / &10 * r * t + &2 * r - &457 / &250) +
                &2 / &5 * (&7 / &10 * r pow 2 + &27 / &10 * r * t) <= &0`
    ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
    NLIN_TAC [SQ_NONNEG `r - &1`];
    ALL_TAC] THEN
  MATCH_MP_TAC MWLM_QUARTIC_CHORD THEN EXISTS_TAC `Z:real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: margins *)
let MWLM_MARGINS = prove
 (`forall c s r t z.
      &0 < r /\ &0 <= t /\ r pow 2 + t pow 2 = &1 /\ &0 <= z /\ z <= &1 / &5 /\
      (&1 + c) * z = s /\ s * z = &1 - c /\
      r * t * z < &1 - r - &43 / &500 * t pow 2
      ==> &0 <= c * r + s * t - &543 / &500 * r + &7 / &20 * (c - s) * (c * t - s * r) \/
          &0 <= r * (c * r + s * t - &543 / &500 * r +
                     &7 / &20 * (c - s) * (c * t - s * r)) + r - &457 / &500`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = c * r + s * t - &543 / &500 * r + &7 / &20 * (c - s) * (c * t - s * r)` THEN
  SUBGOAL_THEN `(&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * s = &2 * z`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `(&1 + c) * z = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z pow 2) pow 2 * f = mwlm_marker r t z` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC MWLM_DEFS THEN
    UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r <= &457 / &500` THENL
   [DISJ1_TAC THEN
    MP_TAC(SPECL [`r:real`; `t:real`; `z:real`] MWLM_SMALL_COSINE) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term ((=) `mwlm_marker`)) (concl th))) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `(&1 + z pow 2) pow 2` THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO];
    DISJ2_TAC THEN
    MP_TAC(SPECL [`r:real`; `t:real`; `z:real`] MWLM_LARGE_COSINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `mwlm_wall r t z = (&1 + z pow 2) pow 2 * (r * f + r - &457 / &500)`
      SUBST1_TAC THENL
     [REWRITE_TAC[mwlm_wall] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term ((=) `mwlm_marker`)) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `(&1 + z pow 2) pow 2` THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;
