(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeRecipientWallScalars.lean    *)
(* (namespace N12Compact.C1092MPPMNegativeRecipientWall.Scalars; Lean        *)
(* header: "Source only").  Exact scalar comparisons for                     *)
(* NEGATIVE-MISSING-POSITIVE-ENDING Theorem 1.  C977CornerCubic.Normal:      *)
(* c977cc_normal; normal_bounds: C977CC_NORMAL_BOUNDS; half (WallProfile-    *)
(* Scalars): C1092WPS_half; quarter_data: C1092WPS_QUARTER_DATA;             *)
(* C1092MPPMCrosspointSupport.half / half_order: c1092mcbh_half /            *)
(* C1092MCBH_HALF_ORDER; C977CornerSectorBounds.cosine_order:                *)
(* C977CSB_COSINE_ORDER; UnitCircleChord.increasing: CCUCC_INCREASING.       *)
(* The private poly is c1092nrws_poly.  Tag C1092NRWS_.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: weak_bounds *)
let C1092NRWS_WEAK_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ &237 / &763 < C1092WPS_half d t
     ==> &7 / &10 < d /\ d < &33 / &40 /\ &283 / &500 < t /\ t < &71 / &100 /\
         &139 / &100 < d + t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&263000 / &319169) (&180831 / &319169)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `&180831 / &319169 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`d:real`; `t:real`; `&263000 / &319169`; `&180831 / &319169`] C1092MCBH_HALF_ORDER) THEN
    ASM_REWRITE_TAC[c1092mcbh_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `&237 / &763 < C1092WPS_half d t` THEN REWRITE_TAC[C1092WPS_half] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC (SPECL [`d:real`; `t:real`; `&263000 / &319169`; `&180831 / &319169`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  MP_TAC (SPECL [`d:real`; `t:real`; `&263000 / &319169`; `&180831 / &319169`; `&1`; `&1`]
            CCUCC_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= (d - t) * (d + t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REPEAT CONJ_TAC THENL
   [NLIN_TAC []; RASM_ARITH_TAC; RASM_ARITH_TAC;
    NLIN_TAC [SQ_NONNEG `t - &71 / &100`]; RASM_ARITH_TAC]);;

(* Lean: poly (private) *)
let c1092nrws_poly = new_definition
 `c1092nrws_poly (x:real) = &43 - &250 * x - &957 * x pow 2 + &1250 * x pow 3`;;

(* Lean: poly_positive (private) *)
let C1092NRWS_POLY_POSITIVE = prove
 (`forall x. &0 <= x /\ x pow 2 + &8 * x <= &1 ==> &0 < c1092nrws_poly x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x <= &77 / &625` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (x - &77 / &625) * (x + &77 / &625 + &8)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x pow 2 + &8 * x <= &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x * x <= &1 / &8 * x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &250 + &957 * (&77 / &625 + x) - &1250 * ((&77 / &625) pow 2 + (&77 / &625) * x + x pow 2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `x * x <= &1 / &8 * x` THEN UNDISCH_TAC `x <= &77 / &625` THEN
    UNDISCH_TAC `&0 <= x` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&77 / &625 - x) * (&250 + &957 * (&77 / &625 + x) -
                 &1250 * ((&77 / &625) pow 2 + (&77 / &625) * x + x pow 2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092nrws_poly] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* Lean: upward_margin *)
let C1092NRWS_UPWARD_MARGIN = prove
 (`forall d t b r. c977cc_normal d t /\ c977cc_normal b r /\ &0 < r /\ &4 * r <= b /\ &2 * d <= &3 * t
     ==> &0 < b * (d * b + t * r) + t - &2 * (d * b + t * r) - b * t +
              (&543 / &500) * t * r + b * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC (SPECL [`b:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal b r`)) THEN
  SUBGOAL_THEN `&97 / &100 < b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (b - &4 * r) * (b + &4 * r) /\ &0 <= (&97 / &100 - b) * (&97 / &100 + b)`
      MP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC (SPECL [`b:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = C1092WPS_half b r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC (SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 + &8 * x <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (b - &4 * r) * (&1 + x pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(&1 + x pow 2) * b = &1 - x pow 2`; `(&1 + x pow 2) * r = &2 * x`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC (SPEC `x:real` C1092NRWS_POLY_POSITIVE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(&1 + x pow 2) * ((&2 / &3) * (b - &457 / &500) + x * (&2 / &3 - b)) =
                c1092nrws_poly x / &750` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + x pow 2) * b = &1 - x pow 2` THEN REWRITE_TAC[c1092nrws_poly] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&2 / &3) * (b - &457 / &500) + x * (&2 / &3 - b)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`&1 + x pow 2`; `--((&2 / &3) * (b - &457 / &500) + x * (&2 / &3 - b))`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(&1 + x pow 2) * ((&2 / &3) * (b - &457 / &500) + x * (&2 / &3 - b)) =
                 c1092nrws_poly x / &750` THEN
    UNDISCH_TAC `&0 < c1092nrws_poly x` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (t - (&2 / &3) * d) * (b - &457 / &500 + x) /\
                &0 < d * ((&2 / &3) * (b - &457 / &500) + x * (&2 / &3 - b))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t * (b - &457 / &500) + x * (t - b * d)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= (t - (&2 / &3) * d) * (b - &457 / &500 + x)`;
      `&0 < d * ((&2 / &3) * (b - &457 / &500) + x * (&2 / &3 - b))`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x * r = &1 - b` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + b) * (x * r - (&1 - b)) = &0` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`x * (&1 + b) = r`; `b pow 2 + r pow 2 = &1`] THEN CONV_TAC REAL_RING;
      REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THENL [RASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r * (t * (b - &457 / &500) + x * (t - b * d))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC (REAL_ARITH `a = b ==> &0 < a ==> &0 < b`) THEN
  UNDISCH_TAC `x * r = &1 - b` THEN CONV_TAC REAL_RING);;

(* Lean: boundary_margin *)
let C1092NRWS_BOUNDARY_MARGIN = prove
 (`forall d t b r. c977cc_normal d t /\ c977cc_normal b r /\ &0 < r /\ &4 * r <= b /\
     d < &33 / &40 /\ &283 / &500 < t /\ t < &71 / &100 /\ &139 / &100 < d + t
     ==> &0 < (d * b + t * r) + (t * b - d * r) - (&543 / &500) * b +
              (&13 / &50) * (t * b - d * r) * t - (d * b + t * r) * (t - (&14 / &25) * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC (SPECL [`b:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal b r`)) THEN
  SUBGOAL_THEN `d * t <= &1 / &2` ASSUME_TAC THENL
   [MP_TAC (SPEC `d - t` REAL_LE_POW_2) THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 <= &1 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (d - t) * (d + t)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&107 / &500 < d + t - &263 / &500 - d * t - (&3 / &10) * t pow 2` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&12 / &25) < t - d - t pow 2 + (&3 / &10) * d * t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&71 / &100 - t) * (&71 / &100 + t - &1) /\
                  &0 < (&33 / &40 - d) * (&1 - (&3 / &10) * t)` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&283 / &500 < t` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b * ((d + t - &263 / &500 - d * t - (&3 / &10) * t pow 2) - &107 / &500) /\
                &0 < r * ((t - d - t pow 2 + (&3 / &10) * d * t) + &12 / &25)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(d * b + t * r) + (t * b - d * r) - (&543 / &500) * b +
                (&13 / &50) * (t * b - d * r) * t - (d * b + t * r) * (t - (&14 / &25) * d) =
                b * (d + t - &263 / &500 - d * t - (&3 / &10) * t pow 2) +
                r * (t - d - t pow 2 + (&3 / &10) * d * t)` SUBST1_TAC THENL
   [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < b * ((d + t - &263 / &500 - d * t - (&3 / &10) * t pow 2) - &107 / &500)`;
    `&0 < r * ((t - d - t pow 2 + (&3 / &10) * d * t) + &12 / &25)`;
    `&4 * r <= b`; `&0 < r`] THEN
  REAL_ARITH_TAC);;
