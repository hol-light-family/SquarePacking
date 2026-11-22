(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingBoundaryShallowScalars.lean    *)
(* (N12Compact.C1092MPPMMissingBoundaryShallow).  Exact scalar comparisons   *)
(* in C1092-MPPM-MISSING-BOUNDARY-SHALLOW-ANGLE, sections 4--6.  Normal is    *)
(* c977cc_normal; CommonCases bounds is CCCS_BOUNDS.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let C1092MBS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C1092MBS_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: crossCos *)
let c1092mbs_crossCos = new_definition
 `c1092mbs_crossCos (c:real) s b r = c * b - s * r`;;

(* Lean: crossSin *)
let c1092mbs_crossSin = new_definition
 `c1092mbs_crossSin (c:real) s b r = c * r + s * b`;;

let C1092MBS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

(* Lean: strict_bounds *)
let C1092MBS_STRICT_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &0 < s
     ==> &7 / &10 < c /\ c < &1 /\ s < &177 / &250 /\ &1 < c + s /\ c + s <= &99 / &70`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  C1092MBS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C1092MBS_PROD `&0 < s * s` THEN C1092MBS_PROD `&0 < c * s` THEN
  C1092MBS_PROD `&0 <= (c - s) * (c + s)` THEN
  C1092MBS_PROD `&0 <= (c - s) * (c - s)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MBS_PROD `&0 <= (c - &1) * c` THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MBS_PROD `&0 <= (s - &177 / &250) * (s + &177 / &250)` THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MBS_PROD `&0 <= (&1 - (c + s)) * (c + s)` THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MBS_PROD `&0 < (c + s - &99 / &70) * (c + s + &99 / &70)` THEN ASM_REAL_ARITH_TAC]);;

let C1092MBS_BOUNDS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th ->
      let x,y = dest_pair(mk_pair(rand(rator(concl th)),rand(concl th))) in
      MP_TAC(SPECL [x; y] C1092MBS_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC) ns) THEN
  C1092MBS_NORMAL_TAC;;

(* Lean: cross_bounds *)
let C1092MBS_CROSS_BOUNDS = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &0 < s /\ &0 < r
     ==> &0 <= c1092mbs_crossCos c s b r /\ &0 < c1092mbs_crossSin c s b r /\
         c1092mbs_crossCos c s b r <= b /\ r <= c1092mbs_crossSin c s b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MBS_BOUNDS_TAC THEN
  REWRITE_TAC[c1092mbs_crossCos; c1092mbs_crossSin] THEN
  C1092MBS_PROD `&0 <= (c - s) * b` THEN C1092MBS_PROD `&0 <= s * (b - r)` THEN
  C1092MBS_PROD `&0 <= b * (&1 - c)` THEN C1092MBS_PROD `&0 <= s * r` THEN
  C1092MBS_PROD `&0 <= r * (c + s - &1)` THEN C1092MBS_PROD `&0 < c * r` THEN
  C1092MBS_PROD `&0 <= s * b` THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: sum_gap (private) *)
let C1092MBS_SUM_GAP = prove
 (`forall b r. c977cc_normal b r /\ &0 < r ==> (&207 / &250) * b * r < b + r - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MBS_BOUNDS_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < b + r - &1 - (&207 / &250) * b * r
                           ==> (&207 / &250) * b * r < b + r - &1`) THEN
  MATCH_MP_TAC C1092MBS_POS_OF_MUL THEN EXISTS_TAC `&1 + b + r` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + b + r) * (b + r - &1 - (&207 / &250) * b * r) =
                (b * r) * (&2 - (&207 / &250) * (&1 + b + r))` SUBST1_TAC THENL
  [UNDISCH_TAC `b * b + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MBS_PROD `&0 < (b * r) * (&2 - (&207 / &250) * (&1 + b + r))` THEN
  ASM_REWRITE_TAC[]);;

(* Lean: northwest_margin *)
let C1092MBS_NORTHWEST_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &0 < s /\ &0 < r
     ==> &0 < b + r - &2 + b pow 2 +
              r * (c1092mbs_crossCos c s b r * (&1 - c - s / &2) +
                   c1092mbs_crossSin c s b r * (&1 - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `r:real`] C1092MBS_CROSS_BOUNDS) THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MBS_SUM_GAP) THEN
  ASM_REWRITE_TAC[c1092mbs_crossCos; c1092mbs_crossSin] THEN REPEAT STRIP_TAC THEN
  C1092MBS_BOUNDS_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `c + s / &2 < &1119 / &1000` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MBS_PROD `&0 <= (c + s / &2 - &1119 / &1000) * (c + s / &2 + &1119 / &1000)` THEN
   C1092MBS_PROD `&0 <= (c - &2 * s) * (c - &2 * s)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MBS_PROD `&0 <= (c * b - s * r) * (&1 - c - s / &2 + &119 / &1000)` THEN
  C1092MBS_PROD `&0 < (c * r + s * b) * (&1 - s - &73 / &250)` THEN
  SUBGOAL_THEN `--(&119 / &1000) * b + (&73 / &250) * r <
                (c * b - s * r) * (&1 - c - s / &2) + (c * r + s * b) * (&1 - s)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MBS_PROD `&0 < r * (((c * b - s * r) * (&1 - c - s / &2) + (c * r + s * b) * (&1 - s)) -
                          (--(&119 / &1000) * b + (&73 / &250) * r))` THEN
  C1092MBS_PROD `&0 <= r * (b - r)` THEN C1092MBS_PROD `&0 < b * r` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: central_margin *)
let C1092MBS_CENTRAL_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &0 < s /\ &0 < r
     ==> &0 < c1092mbs_crossSin c s b r * (b + r) + r - &2 * c1092mbs_crossSin c s b r +
              s * (b - r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MBS_BOUNDS_TAC THEN
  REWRITE_TAC[c1092mbs_crossSin] THEN
  SUBGOAL_THEN `&0 < &2 * b + r - &2` ASSUME_TAC THENL
  [MATCH_MP_TAC C1092MBS_POS_OF_MUL THEN EXISTS_TAC `&1 + b` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + b) * (&2 * b + r - &2) = r * (&1 + b - &2 * r)` SUBST1_TAC THENL
   [UNDISCH_TAC `b * b + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MBS_PROD `&0 < (&1 - b) * (&1 - r)` THEN
  C1092MBS_PROD `&0 <= (c - b) * (c - b)` THEN C1092MBS_PROD `&0 <= (s - r) * (s - r)` THEN
  SUBGOAL_THEN `&0 < r * r - (&1 - b) * (b + r) /\ &0 <= &1 - c * b - s * r`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MBS_PROD `&0 < (r * c) * (&2 * b + r - &2)` THEN
  C1092MBS_PROD `&0 <= s * (r * r - (&1 - b) * (b + r))` THEN
  C1092MBS_PROD `&0 <= r * (&1 - c * b - s * r)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: angle_floors *)
let C1092MBS_ANGLE_FLOORS = prove
 (`forall c s. c977cc_normal c s /\ &0 < s
     ==> &457 / &500 < c + s - c * s /\ &1 / &2 <= c - s + s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MBS_BOUNDS_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MBS_PROD `&0 <= (&99 / &70 - (c + s)) * (&99 / &70 + (c + s) - &2)` THEN
  C1092MBS_PROD `&0 <= (c - s) * (&2 - (c + s))` THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: boundary_margin (private) *)
let C1092MBS_BOUNDARY_MARGIN = prove
 (`forall b r. c977cc_normal b r /\ &0 < r /\ b <= &4 * r
     ==> &0 < b + r - &543 / &500 + (&43 / &250) * r pow 2 - b * r / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MBS_BOUNDS_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MBS_PROD `&0 <= (&4 * r - b) * (&4 * b - r)` THEN
  SUBGOAL_THEN `&6 / &5 < b + r` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MBS_PROD `&0 <= (&6 / &5 - (b + r)) * (&6 / &5 + (b + r))` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MBS_PROD `&0 <= ((b + r) - &6 / &5) * (&7 / &10 - (b + r) / &4)` THEN
  C1092MBS_PROD `&0 <= r * r` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: northeast_margin *)
let C1092MBS_NORTHEAST_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &0 < s /\ &0 < r /\ b <= &4 * r
     ==> &0 < b + r - &2 - b * r + (&543 / &500) * r pow 2 +
              b pow 2 * (c + s - c * s) + b * r * (c - s + s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MBS_ANGLE_FLOORS) THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MBS_BOUNDARY_MARGIN) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  C1092MBS_BOUNDS_TAC THEN
  C1092MBS_PROD `&0 <= (b * b) * ((c + s - c * s) - &457 / &500)` THEN
  C1092MBS_PROD `&0 <= (b * r) * ((c - s + s * s) - &1 / &2)` THEN
  ASM_REAL_ARITH_TAC);;
