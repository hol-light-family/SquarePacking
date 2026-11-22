(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardSmallThreeScalars.lean         *)
(* (N12Compact.C1092MPPMInwardSmallThree).  SMALL-INWARD-THREE-SQUARE-ENDING *)
(* section 2.  Normal: c977cc_normal; half: C1092WPS_half (quarter_data:     *)
(* C1092WPS_QUARTER_DATA; BottomAngle.half_identity: C1092IFBS_HALF_IDENTITY);*)
(* cosH / sinH: c1092sps_cosH / c1092sps_sinH (the substitution c = cosH x,  *)
(* s = sinH x is used through the equivalent quarter_data equations);       *)
(* G01Quartic poly / bernstein: c1092g01q_poly / C1092G01Q_BERNSTEIN;        *)
(* UnitCircleChord.decreasing: CCUCC_DECREASING; cosine_order:               *)
(* C977CSB_COSINE_ORDER.  Tag C1092ISTS_.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomAngle.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG01Quartic.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: Q, J0, kappa, delta, FC, FE (definitions) *)
let c1092ists_Q = new_definition
 `c1092ists_Q (c:real) (s:real) = &1 - c + (&2 / &5) * s`;;
let c1092ists_J0 = new_definition
 `c1092ists_J0 (c:real) (s:real) = c + s - &1 - c * s + (&2 / &5) * s pow 2`;;
let c1092ists_kappa = new_definition
 `c1092ists_kappa (c:real) (s:real) (d:real) (t:real) = c * d + s * t`;;
let c1092ists_delta = new_definition
 `c1092ists_delta (c:real) (s:real) (d:real) (t:real) = c * t - s * d`;;
let c1092ists_FC = new_definition
 `c1092ists_FC c s d t = c1092ists_Q c s + c1092ists_kappa c s d t * (&1 - d - t) +
                         c1092ists_delta c s d t * (&1 - t + (&2 / &5) * d)`;;
let c1092ists_FE = new_definition
 `c1092ists_FE c s d t = &1 - d - t + c1092ists_kappa c s d t * c1092ists_Q c s +
                         c1092ists_delta c s d t`;;

let C1092ISTS_DEFS = [c1092ists_Q; c1092ists_J0; c1092ists_kappa; c1092ists_delta;
                      c1092ists_FC; c1092ists_FE];;

let C1092ISTS_LIN = NLIN_TAC ~deg2:false [];;

let C1092ISTS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   (MATCH_ACCEPT_TAC REAL_LE_POW_2 ORELSE C1092ISTS_LIN); ALL_TAC];;

(* normal bounds, unit equation and the quarter data of x = half c s *)
let C1092ISTS_SETUP_TAC =
  FIRST_ASSUM(fun th -> if can (term_match [] `c977cc_normal c s`) (concl th) then
     STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
     STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) else NO_TAC) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC `C1092WPS_half c s` REAL_LE_POW_2) THEN DISCH_TAC;;

(* Lean: small_bounds *)
let C1092ISTS_SMALL_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &53 / &500
     ==> &97 / &100 < c /\ s < &21 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ISTS_SETUP_TAC THEN
  ABBREV_TAC `x = C1092WPS_half c s` THEN
  C1092ISTS_PROD `&0 <= (&53 / &500 - x) * (&53 / &500 + x)` THEN
  C1092ISTS_PROD `&0 <= (&53 / &500 - x) * (&2 - (&21 / &100) * (x + &53 / &500))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [C1092ISTS_PROD `&0 <= (&1 + x * x) * (&97 / &100 - c)`;
    C1092ISTS_PROD `&0 <= (&1 + x * x) * (s - &21 / &100)`] THEN
  C1092ISTS_LIN);;

(* Lean: j_bounds *)
let C1092ISTS_J_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &0 < s /\
         &0 < C1092WPS_half c s pow 2 - &2 * C1092WPS_half c s + &1 / &5
     ==> c1092ists_J0 c s < &0 /\ --c1092ists_J0 c s <= s pow 2 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFBS_HALF_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092ISTS_SETUP_TAC THEN
  ABBREV_TAC `x = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + x pow 2) * (c1092ists_Q c s - x) = --x * (x pow 2 - &2 * x + &1 / &5)`
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092ists_Q] THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092ISTS_PROD `&0 < x * (x pow 2 - &2 * x + &1 / &5)` THEN
  SUBGOAL_THEN `c1092ists_Q c s - x < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092ISTS_PROD `&0 <= (&1 + x pow 2) * (c1092ists_Q c s - x)` THEN C1092ISTS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c1092ists_J0 c s = s * (c1092ists_Q c s - x)` SUBST1_TAC THENL
   [REWRITE_TAC[c1092ists_J0; c1092ists_Q] THEN
    UNDISCH_TAC `&1 - c = s * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `a < &0 <=> &0 < --a`] THEN
    REWRITE_TAC[REAL_ARITH `--(s * y) = s * --y`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + c) * (s pow 2 / &10 + s * (c1092ists_Q c s - x)) = s pow 2 * (c + &2 * s - &1) / &2`
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092ists_Q] THEN
    UNDISCH_TAC `&1 - c = s * x` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092ISTS_PROD `&0 <= s pow 2 * (c + &2 * s - &1)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092ISTS_PROD `&0 < (&1 + c) * --(s pow 2 / &10 + s * (c1092ists_Q c s - x))` THEN
  C1092ISTS_LIN);;

(* Lean: endpoint_first (private) *)
let C1092ISTS_ENDPOINT_FIRST = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &53 / &500
     ==> &0 < c1092ists_FC c s (&15 / &17) (&8 / &17)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ISTS_SETUP_TAC THEN
  ABBREV_TAC `x = C1092WPS_half c s` THEN
  C1092ISTS_PROD `&0 <= (&53 / &500 - x) * (&1574 - &2740 * (x + &53 / &500))` THEN
  SUBGOAL_THEN `&0 < &150 - &1574 * x + &2740 * x pow 2` ASSUME_TAC THENL
   [C1092ISTS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&1445 * (&1 + x pow 2) * c1092ists_FC c s (&15 / &17) (&8 / &17) =
                &150 - &1574 * x + &2740 * x pow 2` ASSUME_TAC THENL
   [REWRITE_TAC C1092ISTS_DEFS THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092ISTS_PROD `&0 <= (&1445 * (&1 + x pow 2)) * --c1092ists_FC c s (&15 / &17) (&8 / &17)` THEN
  C1092ISTS_LIN);;

(* Lean: endpoint_last (private) *)
let C1092ISTS_ENDPOINT_LAST = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &53 / &500
     ==> &0 < c1092ists_FE c s (&15 / &17) (&8 / &17)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ISTS_SETUP_TAC THEN
  ABBREV_TAC `x = C1092WPS_half c s` THEN
  MP_TAC(SPECL [`&9`; `--(&90)`; `&154`; `--(&50)`; `--(&220)`; `&53 / &500`; `x:real`]
    C1092G01Q_BERNSTEIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[c1092g01q_poly] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `&85 * (&1 + x pow 2) pow 2 * c1092ists_FE c s (&15 / &17) (&8 / &17) =
                &10 - &90 * x + &154 * x pow 2 - &50 * x pow 3 - &220 * x pow 4` ASSUME_TAC THENL
   [REWRITE_TAC C1092ISTS_DEFS THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &85 * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[C1092SPS_HALF_DEN_POS]; ALL_TAC] THEN
  C1092ISTS_PROD `&0 <= (&85 * (&1 + x pow 2) pow 2) * --c1092ists_FE c s (&15 / &17) (&8 / &17)` THEN
  C1092ISTS_LIN);;

(* Lean: first_margin *)
let C1092ISTS_FIRST_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ C1092WPS_half c s <= &53 / &500 /\
             &8 / &17 <= t
     ==> &0 < c1092ists_FC c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ISTS_ENDPOINT_FIRST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal c s`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal d t`)) THEN
  ABBREV_TAC `H = (d + &15 / &17) / &2` THEN ABBREV_TAC `TT = (t + &8 / &17) / &2` THEN
  SUBGOAL_THEN `&0 < H /\ &0 <= TT /\ H <= &1 /\ TT <= &1 /\ &0 <= H - TT /\ H + TT <= &10 / &7`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "TT"] THEN REPEAT CONJ_TAC THEN C1092ISTS_LIN; ALL_TAC] THEN
  C1092ISTS_PROD `&0 <= (c * (H - TT)) * (&1 - (&3 / &5) * (H + TT))` THEN
  C1092ISTS_PROD `&0 <= H * (&1 - (&3 / &5) * TT)` THEN
  C1092ISTS_PROD `&0 <= TT * (&1 - (&3 / &5) * H)` THEN
  C1092ISTS_PROD `&0 <= s * (H + TT - (&6 / &5) * H * TT)` THEN
  C1092ISTS_PROD `&0 <= (t - &8 / &17) *
     (c * (H - TT) * (&1 - (&3 / &5) * (H + TT)) + s * (H + TT - (&6 / &5) * H * TT))` THEN
  SUBGOAL_THEN `H * (c1092ists_FC c s d t - c1092ists_FC c s (&15 / &17) (&8 / &17)) =
     (t - &8 / &17) * (c * (H - TT) * (&1 - (&3 / &5) * (H + TT)) + s * (H + TT - (&6 / &5) * H * TT))`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "TT"] THEN REWRITE_TAC C1092ISTS_DEFS THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092ISTS_PROD `&0 < H * (c1092ists_FC c s (&15 / &17) (&8 / &17) - c1092ists_FC c s d t)` THEN
  C1092ISTS_LIN);;

(* Lean: last_margin *)
let C1092ISTS_LAST_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ C1092WPS_half c s <= &53 / &500 /\
             &8 / &17 <= t
     ==> &0 < c1092ists_FE c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ISTS_ENDPOINT_LAST) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ISTS_SMALL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&15 / &17`; `&8 / &17`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal c s`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal d t`)) THEN
  ABBREV_TAC `A = &1 + s - c * c1092ists_Q c s` THEN
  ABBREV_TAC `B = &1 - c - s * c1092ists_Q c s` THEN
  SUBGOAL_THEN `&97 / &100 < A` ASSUME_TAC THENL
   [C1092ISTS_PROD `&0 <= (c - &97 / &100) * (c + &97 / &100 - &1)` THEN
    C1092ISTS_PROD `&0 <= s * (&1 - (&2 / &5) * c)` THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[c1092ists_Q] THEN C1092ISTS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `B <= s pow 2 / &10` ASSUME_TAC THENL
   [C1092ISTS_PROD `&0 <= s pow 2 * (c + &2 * s - &1)` THEN
    SUBGOAL_THEN `(&1 + c) * (s pow 2 / &10 - B) = s pow 2 * (c + &2 * s - &1) / &2` ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[c1092ists_Q] THEN
      UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092ISTS_PROD `&0 < (&1 + c) * (B - s pow 2 / &10)` THEN C1092ISTS_LIN; ALL_TAC] THEN
  C1092ISTS_PROD `&0 < (&21 / &100 - s) * (&21 / &100 + s)` THEN
  SUBGOAL_THEN `B < &441 / &100000` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092ISTS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `A * d + B * t <= A * (&15 / &17) + B * (&8 / &17)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= B` THENL
     [MATCH_MP_TAC CCUCC_DECREASING THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN C1092ISTS_LIN;
      C1092ISTS_PROD `&0 <= A * (&15 / &17 - d)` THEN
      C1092ISTS_PROD `&0 <= (t - &8 / &17) * --B` THEN C1092ISTS_LIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092ists_FE c s d t = &1 - A * d - B * t /\
                c1092ists_FE c s (&15 / &17) (&8 / &17) = &1 - A * (&15 / &17) - B * (&8 / &17)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC C1092ISTS_DEFS THEN
    CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092ISTS_LIN);;
