(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/PositiveEndingScalars.lean          *)
(* (namespace N12Compact.Completion.OtherCases.PositiveEndingScalars).      *)
(* Scalar margins for the positive southeast ending.  half / quarter_data:  *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA; CanonicalScalars.bounds:          *)
(* CCCS_BOUNDS.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_InwardSignScalars.ml";;

(* Lean: dot_lt (private) *)
let OCPES_DOT_LT = prove
 (`forall d r x y R. d pow 2 + r pow 2 = &1 /\ &0 < R /\ x pow 2 + y pow 2 < R pow 2
               ==> d * x + r * y < R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d * x + r * y) pow 2 + (d * y - r * x) pow 2 = x pow 2 + y pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (d * x + r * y - R) * (d * x + r * y + R)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d * y - r * x` REAL_LE_POW_2) THEN
  UNDISCH_TAC `(d * x + r * y) pow 2 + (d * y - r * x) pow 2 = x pow 2 + y pow 2` THEN
  UNDISCH_TAC `x pow 2 + y pow 2 < R pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: bar_bounds *)
let OCPES_BAR_BOUNDS = prove
 (`forall c s. &9 / &10 < c /\ &0 < s /\ s < &43 / &100 /\ c pow 2 + s pow 2 = &1
         ==> (c - &1) * (c + s) + &13 / &50 * s pow 2 < &0 /\
             (c - &1) * (c - s) + &13 / &50 * c * s < &7 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    DISCH_TAC THEN DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < s pow 2 * ((c + s) - &13 / &50 * (&1 + c))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&1 + c) * ((c - &1) * (c + s) + &13 / &50 * s pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + c) * ((c - &1) * (c + s) + &13 / &50 * s pow 2) =
                  --(s pow 2 * ((c + s) - &13 / &50 * (&1 + c)))` SUBST1_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    UNDISCH_TAC `&0 < s pow 2 * ((c + s) - &13 / &50 * (&1 + c))` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `s pow 2 / &2 <= &1 - c /\
                  &0 <= (&1 - c) * (c - s - &47 / &100) /\ &0 <= s * (&1 - c) /\
                  &0 < (&43 / &100 - s) * (&13 / &50 - &47 / &200 * (&43 / &100 + s))`
      MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(SPEC `c - &1` REAL_LE_POW_2) THEN
        UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
    NLIN_TAC []]);;

(* Lean: bar_norm *)
let OCPES_BAR_NORM = prove
 (`forall c s d r. &9 / &10 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ d pow 2 + r pow 2 = &1
             ==> d * ((c - &1) * (c + s) + &13 / &50 * s pow 2) +
                 r * ((c - &1) * (c - s) + &13 / &50 * c * s) < &1 - d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = (c - &1) * (c + s) + &13 / &50 * s pow 2` THEN
  ABBREV_TAC `R = (c - &1) * (c - s) + &13 / &50 * c * s` THEN
  SUBGOAL_THEN `(&1 + c) * ((&1 + D) pow 2 + R pow 2 - &1) =
                s pow 2 * (&6469 / &2500 - &8531 / &2500 * c - &63 / &25 * s)`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "R"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + D) pow 2 + R pow 2 < &1 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_ONE] THEN
    SUBGOAL_THEN `&0 < s pow 2 * --(&6469 / &2500 - &8531 / &2500 * c - &63 / &25 * s)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&1 + c) * ((&1 + D) pow 2 + R pow 2 - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < s pow 2 * --(&6469 / &2500 - &8531 / &2500 * c - &63 / &25 * s)` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `&1 + D`; `R:real`; `&1`] OCPES_DOT_LT) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN REAL_ARITH_TAC);;

(* Lean: floor_norm *)
let OCPES_FLOOR_NORM = prove
 (`forall c s d r. &9 / &10 < c /\ &0 < s /\ s < &1 /\ c pow 2 + s pow 2 = &1 /\
             d pow 2 + r pow 2 = &1
             ==> (&1 - c) * (s * d + c * r - d) < c * (&1 - d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    DISCH_TAC THEN DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(c - (&1 - c) * (&1 - s)) pow 2 + (c * (&1 - c)) pow 2 - c pow 2 =
                &2 * (&1 - c) * (&1 - s) * (&1 - &2 * c)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((&2 * (&1 - c)) * (&1 - s)) * (&2 * c - &1)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `c - (&1 - c) * (&1 - s)`; `c * (&1 - c)`; `c:real`]
    OCPES_DOT_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < ((&2 * (&1 - c)) * (&1 - s)) * (&2 * c - &1)` THEN
    UNDISCH_TAC `(c - (&1 - c) * (&1 - s)) pow 2 + (c * (&1 - c)) pow 2 - c pow 2 =
                &2 * (&1 - c) * (&1 - s) * (&1 - &2 * c)` THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: negative_west_margin *)
let OCPES_NEGATIVE_WEST_MARGIN = prove
 (`forall d r. &0 < d /\ &0 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1 /\ &7 * d < &13 * r
         ==> d - &1 + &7 / &20 * r * (d + r) > &1 / &14 * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `z = C1092WPS_half d r` THEN
  SUBGOAL_THEN `&0 <= z pow 2 /\ &0 < &1 + z pow 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &5 / &12` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 + z pow 2) * (d - r)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (z - &5 / &12) * (z + &5 / &12)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &4 < z` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (&1 + z pow 2) * (&13 * r - &7 * d)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= z * (&1 / &4 - z)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < --(&1) / &14 + &7 / &10 * z - &3 / &5 * z pow 2 - &7 / &10 * z pow 3 -
         &27 / &14 * z pow 4` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `--(&1) / &14 + &7 / &10 * z - &3 / &5 * z pow 2 - &7 / &10 * z pow 3 -
      &27 / &14 * z pow 4 =
      &69093 / &1120 * (&5 / &12 - z) pow 4 +
      &11151 / &40 * (z - &1 / &4) * (&5 / &12 - z) pow 3 +
      &223803 / &560 * (z - &1 / &4) pow 2 * (&5 / &12 - z) pow 2 +
      &54309 / &280 * (z - &1 / &4) pow 3 * (&5 / &12 - z) +
      &303 / &32 * (z - &1 / &4) pow 4` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + z pow 2) pow 2 * (&13 / &14 * d - &1 + &7 / &20 * r * (d + r)) =
    --(&1) / &14 + &7 / &10 * z - &3 / &5 * z pow 2 - &7 / &10 * z pow 3 -
    &27 / &14 * z pow 4` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(&1 + z pow 2) pow 2 * (&13 / &14 * d - &1 + &7 / &20 * r * (d + r)) =
      &13 / &14 * (&1 + z pow 2) * ((&1 + z pow 2) * d) - (&1 + z pow 2) pow 2 +
      &7 / &20 * ((&1 + z pow 2) * r) * ((&1 + z pow 2) * d + (&1 + z pow 2) * r)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_gt; GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(&1 + z pow 2) pow 2`;
                `--(&13 / &14 * d - &1 + &7 / &20 * r * (d + r))`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: large_sum (private) *)
let OCPES_LARGE_SUM = prove
 (`forall d r. &0 < d /\ &13 / &20 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1
         ==> &176 / &125 < d + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (d - r) * (d + r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &5 / &7` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (r - &5 / &7) * (r + &5 / &7)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&176 / &125 - r - d) * (&176 / &125 - r + d) /\
                &0 <= (r - &13 / &20) * (&379 / &500 - r)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* r * x < r * y - k  ==>  x < y - k / r  for r > 0 *)
let OCPES_DIVIDE = prove
 (`forall r x y k. &0 < r /\ r * x < r * y - k ==> x < y - k / r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r * (k / r) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`r:real`; `y - k / r`; `x:real`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

(* Lean: positive_west_margin *)
let OCPES_POSITIVE_WEST_MARGIN = prove
 (`forall d r. &0 < d /\ &0 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1
         ==> (&7 / &200 < &7 / &20 * (d - r) \/
              &7 / &200 < &7 / &20 * (d - r) + &1 - (&13 / &20) / r) /\
             (&12 / &113 * (&1 - r) < &7 / &20 * (d - r) \/
              &12 / &113 * (&1 - r) < &7 / &20 * (d - r) + &1 - (&13 / &20) / r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= &13 / &20` THENL
   [SUBGOAL_THEN `&759 / &1000 < d` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (&759 / &1000 - d) * (&759 / &1000 + d) /\
                    &0 <= (&13 / &20 - r) * (&13 / &20 + r)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &5 / &7` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (d - r) * (d + r) /\ &0 < (r - &5 / &7) * (r + &5 / &7)`
      MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`] OCPES_LARGE_SUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= (r - &13 / &20) * (&5 / &7 - r) /\
                &0 < r * (d + r - &176 / &125)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN DISJ2_TAC THEN
  REWRITE_TAC[REAL_ARITH `x + &1 - k / r = (x + &1) - k / r`] THEN
  MATCH_MP_TAC OCPES_DIVIDE THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let t = concl th in is_real_rel t &&
    (can (find_term ((=) `d:real`)) t || can (find_term ((=) `r:real`)) t) &&
    not (is_neg t)))) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC []);;
