(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/UpperThirdScalars.lean              *)
(* (N12Compact.C1092MMMPUpperThirdScalars).  The continuous scalar           *)
(* inequality in NORTHEAST-UPPER-THIRD 4.3.  Normal: c977cc_normal;          *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;               *)
(* cosine_order / sine_order: C977CSB_COSINE_ORDER / C977CSB_SINE_ORDER.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_FinalScalars39.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092UTS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092UTS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092UTS_LIN_TAC; DISCH_TAC];;

let C1092UTS_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092UTS_LIN_TAC; DISCH_TAC];;

let C1092UTS_NORMAL_TAC = C977CSB_NORMAL_TAC;;

(* Lean: margin *)
let c1092uts_margin = new_definition
 `c1092uts_margin (d:real) r b t =
    &1 - b - t + (b * d + t * r) * (&1 - d + (&2 / &5) * r) + (&23 / &25) * (t * d - b * r)`;;

(* Lean: derivative *)
let c1092uts_derivative = new_definition
 `c1092uts_derivative (d:real) r b t =
    t - b - (t * d - b * r) * (&1 - d + (&2 / &5) * r) + (&23 / &25) * (b * d + t * r)`;;

(* Lean: shallow_bounds *)
let C1092UTS_SHALLOW_BOUNDS = prove
 (`forall d r. c977cc_normal d r /\ &8 * r < &7 * d ==> &3 / &4 < d /\ r < &2 / &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092UTS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092UTS_LT_MUL_TAC `&7 * d - &8 * r` `&7 * d + &8 * r` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [C1092UTS_LE_MUL_TAC `&3 / &4 - d` `&3 / &4 + d`;
    C1092UTS_LE_MUL_TAC `r - &2 / &3` `r + &2 / &3`] THEN
  C1092UTS_LIN_TAC);;

(* Lean: cosine_cap *)
let C1092UTS_COSINE_CAP = prove
 (`forall b t. c977cc_normal b t /\ &3 / &5 <= t ==> b <= &4 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092UTS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092UTS_LE_MUL_TAC `t - &3 / &5` `t + &3 / &5` THEN
  MP_TAC(SPEC `b - &4 / &5` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092UTS_LIN_TAC);;

(* Lean: relative_bounds *)
let C1092UTS_RELATIVE_BOUNDS = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t
     ==> &7 / &10 < b * d + t * r /\ t * d - b * r < &71 / &100 /\
         b * d + t * r <= &1 /\
         (b * d + t * r) pow 2 + (t * d - b * r) pow 2 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092UTS_NORMAL_TAC THEN
  SUBGOAL_THEN `(b * d + t * r) pow 2 + (t * d - b * r) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092UTS_LT_MUL_TAC `b:real` `d:real` THEN C1092UTS_LE_MUL_TAC `t:real` `r:real` THEN
  C1092UTS_LE_MUL_TAC `b - t` `d:real` THEN C1092UTS_LE_MUL_TAC `b + t` `r:real` THEN
  C1092UTS_LE_MUL_TAC `b:real` `d - r` THEN C1092UTS_LE_MUL_TAC `t:real` `d + r` THEN
  SUBGOAL_THEN `&0 < b * d + t * r /\ &0 <= (b * d + t * r) - (t * d - b * r) /\
                &0 <= (b * d + t * r) + (t * d - b * r)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092UTS_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall p q. (p:real) pow 2 + q pow 2 = &1 /\ &0 < p /\ &0 <= p - q /\ &0 <= p + q
                ==> &7 / &10 < p /\ q < &71 / &100 /\ p <= &1`
    (fun th -> MATCH_MP_TAC th) THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    C1092UTS_LE_MUL_TAC `p - q` `p + q` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092UTS_LE_MUL_TAC `&7 / &10 - p` `&7 / &10 + p` THEN C1092UTS_LIN_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092UTS_LE_MUL_TAC `q - &71 / &100` `q + &71 / &100` THEN C1092UTS_LIN_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `q:real` REAL_LE_SQUARE) THEN MP_TAC(SPEC `p - &1` REAL_LE_SQUARE) THEN
    REPEAT DISCH_TAC THEN C1092UTS_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_2]);;

(* Lean: derivative_positive (private) *)
let C1092UTS_DERIVATIVE_POSITIVE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &3 / &4 < d /\ r < &2 / &3 /\
             &3 / &5 <= t
             ==> &187 / &2500 < c1092uts_derivative d r b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `b:real`; `t:real`] C1092UTS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092UTS_COSINE_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092UTS_NORMAL_TAC THEN
  REWRITE_TAC[c1092uts_derivative] THEN
  C1092UTS_LE_MUL_TAC `&71 / &100 - (t * d - b * r)` `&1 - d + (&2 / &5) * r` THEN
  C1092UTS_LIN_TAC);;

(* Lean: monotone (private) *)
let C1092UTS_MONOTONE = prove
 (`forall d r b t b0 t0. c977cc_normal d r /\ c977cc_normal b t /\ c977cc_normal b0 t0 /\
                 &3 / &4 < d /\ r < &2 / &3 /\ &3 / &5 <= t0 /\ t0 <= t
                 ==> c1092uts_margin d r b0 t0 <= c1092uts_margin d r b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `b:real`; `t:real`] C1092UTS_DERIVATIVE_POSITIVE) THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `b0:real`; `t0:real`] C1092UTS_DERIVATIVE_POSITIVE) THEN
  SUBGOAL_THEN `&3 / &5 <= t` ASSUME_TAC THENL [C1092UTS_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c1092uts_derivative; c1092uts_margin] THEN REPEAT STRIP_TAC THEN
  C1092UTS_NORMAL_TAC THEN
  ABBREV_TAC `kk = &1 - d * (&1 - d + (&2 / &5) * r) + (&23 / &25) * r` THEN
  ABBREV_TAC `ll = &1 - r * (&1 - d + (&2 / &5) * r) - (&23 / &25) * d` THEN
  SUBGOAL_THEN `&0 <= kk * (t + t0) - ll * (b + b0)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kk"; "ll"] THEN C1092UTS_LIN_TAC; ALL_TAC] THEN
  C1092UTS_LE_MUL_TAC `t - t0` `kk * (t + t0) - ll * (b + b0)` THEN
  SUBGOAL_THEN
   `(b + b0) * ((&1 - b - t + (b * d + t * r) * (&1 - d + (&2 / &5) * r) +
                (&23 / &25) * (t * d - b * r)) -
               (&1 - b0 - t0 + (b0 * d + t0 * r) * (&1 - d + (&2 / &5) * r) +
                (&23 / &25) * (t0 * d - b0 * r))) =
    (t - t0) * (kk * (t + t0) - ll * (b + b0))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kk"; "ll"] THEN
    UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `b0 pow 2 + t0 pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b + b0`;
    `--((&1 - b - t + (b * d + t * r) * (&1 - d + (&2 / &5) * r) +
                (&23 / &25) * (t * d - b * r)) -
               (&1 - b0 - t0 + (b0 * d + t0 * r) * (&1 - d + (&2 / &5) * r) +
                (&23 / &25) * (t0 * d - b0 * r)))`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092UTS_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN C1092UTS_LIN_TAC);;

(* Lean: quartic_positive (private) *)
let C1092UTS_QUARTIC_POSITIVE = prove
 (`forall w. &0 <= w /\ w <= &1 / &3
       ==> &0 < (&19 - &104 * w + &220 * w pow 2 + &36 * w pow 3 - &319 * w pow 4) / &125`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &3 * w /\ &0 <= &1 - &3 * w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&1 - &3 * w) pow 4 /\ &0 <= (&3 * w) * (&1 - &3 * w) pow 3 /\
    &0 <= (&3 * w) pow 2 * (&1 - &3 * w) pow 2 /\ &0 <= (&3 * w) pow 3 * (&1 - &3 * w) /\
    &0 <= (&3 * w) pow 4` MP_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: endpoint_positive (private) *)
let C1092UTS_ENDPOINT_POSITIVE = prove
 (`forall d r. c977cc_normal d r /\ r <= &3 / &5
         ==> &0 < c1092uts_margin d r (&4 / &5) (&3 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&4 / &5) (&3 / &5)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `d:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092UTS_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092UTS_LIN_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half d r`,`w:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `w <= &1 / &3` ASSUME_TAC THENL
   [C1092UTS_LE_MUL_TAC `w:real` `d - &4 / &5` THEN C1092UTS_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `w:real` C1092UTS_QUARTIC_POSITIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&1 + w pow 2) pow 2 * c1092uts_margin d r (&4 / &5) (&3 / &5) =
    (&19 - &104 * w + &220 * w pow 2 + &36 * w pow 3 - &319 * w pow 4) / &125`
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092uts_margin] THEN
    UNDISCH_TAC `(&1 + w pow 2) * d = &1 - w pow 2` THEN
    UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + w pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(&1 + w pow 2) pow 2`; `--c1092uts_margin d r (&4 / &5) (&3 / &5)`]
    REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092UTS_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN C1092UTS_LIN_TAC);;

(* Lean: neighbor_positive *)
let C1092UTS_NEIGHBOR_POSITIVE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &3 / &4 < d /\ r < &2 / &3 /\
             &3 / &5 <= t /\ &0 <= t * d - b * r
             ==> &0 < c1092uts_margin d r b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
   [MP_TAC(SPECL [`d:real`; `r:real`] C1092UTS_ENDPOINT_POSITIVE) THEN
    MP_TAC(SPECL [`d:real`; `r:real`; `b:real`; `t:real`; `&4 / &5`; `&3 / &5`]
      C1092UTS_MONOTONE) THEN
    SUBGOAL_THEN `c977cc_normal (&4 / &5) (&3 / &5)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `t:real`; `d:real`; `r:real`] C977CSB_SINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092UTS_COSINE_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `b:real`; `t:real`; `d:real`; `r:real`]
    C1092UTS_MONOTONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092uts_margin d r d r = &2 - &2 * d - (&3 / &5) * r` SUBST1_TAC THENL
   [REWRITE_TAC[c1092uts_margin] THEN C1092UTS_NORMAL_TAC THEN
    UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REAL_ARITH_TAC);;
