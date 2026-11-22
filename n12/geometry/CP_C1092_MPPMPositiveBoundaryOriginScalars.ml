(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveBoundaryOriginScalars.lean   *)
(* (N12Compact.C1092MPPMPositiveBoundaryOrigin.Scalars).  Full-interval     *)
(* scalar margins for POSITIVE-BOUNDARY-ORIGIN sections 4--5.               *)
(* Normal is c977cc_normal; sine_order / cosine_order are C977CSB_*.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092PBO_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092PBO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; RASM_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LT THEN RASM_ARITH_TAC]; ALL_TAC];;

(* cancellation of a positive factor *)
let C1092PBO_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

let C1092PBO_CANCEL_TAC k =
  MATCH_MP_TAC C1092PBO_CANCEL THEN EXISTS_TAC k THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC];;

(* Lean: endpoint, vMargin, plusPhi, minusPhi, plusMargin, minusMargin *)
let c1092pbo_endpoint = new_definition
 `c1092pbo_endpoint (b:real) (r:real) = &2 * b + r - &2 + r pow 2 - b * r`;;
let c1092pbo_vMargin = new_definition
 `c1092pbo_vMargin (c:real) (s:real) (b:real) (r:real) =
    b + (c * b + s * r) * (b + r - &2) + s * (r - b) + b * max (--(c * r - s * b)) (&0)`;;
let c1092pbo_plusPhi = new_definition
 `c1092pbo_plusPhi (c:real) (s:real) (b:real) (r:real) =
    b * (c - s + s pow 2 / &2) + r * (c + s - &1 - c * s / &2)`;;
let c1092pbo_minusPhi = new_definition
 `c1092pbo_minusPhi (c:real) (s:real) (b:real) (r:real) =
    b * (c + s - c * s) + r * (s - s pow 2 - c)`;;
let c1092pbo_plusMargin = new_definition
 `c1092pbo_plusMargin c s b r = b + r - &2 + r pow 2 + b * c1092pbo_plusPhi c s b r`;;
let c1092pbo_minusMargin = new_definition
 `c1092pbo_minusMargin c s b r = b + r - &2 + r pow 2 + b * c1092pbo_minusPhi c s b r`;;

(* Lean: sum_bounds (private) *)
let C1092PBO_SUM_BOUNDS = prove
 (`forall c s. c977cc_normal c s ==> &1 <= c + s /\ c + s < &17 / &12`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PBO_NORMAL_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PBO_PROD `&0 <= (c + s - &17 / &12) * (c + s + &17 / &12)` THEN
  NLIN_TAC [SQ_NONNEG `c - s:real`]);;

(* Lean: endpoint_positive *)
let C1092PBO_ENDPOINT_POSITIVE = prove
 (`forall b r. c977cc_normal b r /\ &0 < r ==> &0 < c1092pbo_endpoint b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PBO_NORMAL_TAC THEN
  SUBGOAL_THEN `&1 < b + r` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PBO_PROD `&0 <= (&1 - b - r) * (&1 + b + r)` THEN
   C1092PBO_PROD `&0 < b * r` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + b) * c1092pbo_endpoint b r = r pow 2 * (b + r - &1)` ASSUME_TAC THENL
  [REWRITE_TAC[c1092pbo_endpoint] THEN UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092PBO_PROD `&0 < r pow 2 * (b + r - &1)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PBO_PROD `&0 <= (&1 + b) * --c1092pbo_endpoint b r` THEN
  RASM_ARITH_TAC);;

(* Lean: v_positive *)
let C1092PBO_V_POSITIVE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &0 < r
             ==> &0 < c1092pbo_vMargin c s b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092PBO_ENDPOINT_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `forall e v:real. &0 < e /\ e <= v ==> &0 < v`) THEN
  EXISTS_TAC `c1092pbo_endpoint b r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 <= c * r - s * b` THENL
  [MP_TAC(SPECL [`b:real`; `r:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`b:real`; `r:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   C1092PBO_NORMAL_TAC THEN
   SUBGOAL_THEN `c1092pbo_vMargin c s b r =
                 b - (b * (&2 - b - r)) * c - (b - r * (b + r - &1)) * s` SUBST1_TAC THENL
   [REWRITE_TAC[c1092pbo_vMargin] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max (--x) (&0) = &0`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `c1092pbo_endpoint b r =
                 b - (b * (&2 - b - r)) * b - (b - r * (b + r - &1)) * r` SUBST1_TAC THENL
   [REWRITE_TAC[c1092pbo_endpoint] THEN UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   C1092PBO_PROD `&0 < b * (&2 - b - r)` THEN
   C1092PBO_PROD `&0 <= r * (&2 - b - r)` THEN
   SUBGOAL_THEN `&0 <= b - r * (b + r - &1)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PBO_PROD `&0 <= (b - r * (b + r - &1)) * (c - b)` THEN
   C1092PBO_PROD `&0 <= (b * (&2 - b - r)) * (r - s)` THEN
   C1092PBO_PROD `&0 <= b * (b - r)` THEN
   SUBGOAL_THEN `&0 <= (b - r * (b + r - &1)) * (c + b) - (b * (&2 - b - r)) * (r + s)`
   ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PBO_PROD `&0 <= (r - s) *
     ((b - r * (b + r - &1)) * (c + b) - (b * (&2 - b - r)) * (r + s))` THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   C1092PBO_CANCEL_TAC `c + b:real` THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `&0 <= (r - s) * x`) (concl th))) THEN
   MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 <= x ==> &0 <= y`) THEN
   UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   CONV_TAC REAL_RING;
   SUBGOAL_THEN `c * r - s * b <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `r:real`] C977CSB_SINE_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   C1092PBO_NORMAL_TAC THEN
   SUBGOAL_THEN `&2 * (&1 + b * r - b - r) = (b + r - &1) pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= &1 + b * r - b - r` ASSUME_TAC THENL
   [MP_TAC(SPEC `b + r - &1` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c1092pbo_vMargin c s b r =
                 b - b * (&2 - b) * c + (&1 + b * r - b - r) * s` SUBST1_TAC THENL
   [REWRITE_TAC[c1092pbo_vMargin] THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> max (--x) (&0) = --x`] THEN
    UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `c1092pbo_endpoint b r =
                 b - b * (&2 - b) * b + (&1 + b * r - b - r) * r` SUBST1_TAC THENL
   [REWRITE_TAC[c1092pbo_endpoint] THEN UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   C1092PBO_PROD `&0 <= (b * (&2 - b)) * (b - c)` THEN
   C1092PBO_PROD `&0 <= (&1 + b * r - b - r) * (s - r)` THEN
   RASM_ARITH_TAC]);;

(* Lean: plus_positive *)
let C1092PBO_PLUS_POSITIVE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &0 < r /\ &0 <= c * r - s * b
             ==> &0 < c1092pbo_plusMargin c s b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092PBO_ENDPOINT_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092PBO_NORMAL_TAC THEN
  C1092PBO_PROD `&0 <= (b - r) * (c + b)` THEN
  C1092PBO_PROD `&0 <= (b * (r + s)) * (&1 - (c + b) / &2)` THEN
  C1092PBO_PROD `&0 <= (r * (r + s)) * (&1 - r / &2)` THEN
  C1092PBO_PROD `&0 <= (r * c / &2) * (c + b)` THEN
  ABBREV_TAC `J = (b - r) * (c + b) + (b * (r + s)) * (&1 - (c + b) / &2) +
                  (r * (r + s)) * (&1 - r / &2) + (r * c / &2) * (c + b)` THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= (r - s) * J` THEN
  SUBGOAL_THEN `c1092pbo_plusPhi b r b r <= c1092pbo_plusPhi c s b r` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   C1092PBO_CANCEL_TAC `c + b:real` THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `&0 <= (r - s) * J`)) THEN
   MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 <= x ==> &0 <= y`) THEN
   EXPAND_TAC "J" THEN REWRITE_TAC[c1092pbo_plusPhi] THEN
   UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `b + r - &2 + r pow 2 + b * c1092pbo_plusPhi b r b r = c1092pbo_endpoint b r`
  ASSUME_TAC THENL
  [REWRITE_TAC[c1092pbo_plusPhi; c1092pbo_endpoint] THEN
   UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= b * (c1092pbo_plusPhi c s b r - c1092pbo_plusPhi b r b r)` THEN
  REWRITE_TAC[c1092pbo_plusMargin] THEN RASM_ARITH_TAC);;

(* Lean: minus_positive *)
let C1092PBO_MINUS_POSITIVE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ (&5 / &12) * b < r /\
             c * r - s * b <= &0
             ==> &0 < c1092pbo_minusMargin c s b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PBO_SUM_BOUNDS) THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092PBO_SUM_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `r:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PBO_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092PBO_ENDPOINT_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `P = c + b:real` THEN ABBREV_TAC `Q = s + r:real` THEN
  ABBREV_TAC `Z = P - Q:real` THEN ABBREV_TAC `H = P + Q:real` THEN
  ABBREV_TAC `L = H - P * Q:real` THEN
  SUBGOAL_THEN `&0 <= Z /\ &0 <= Q /\ P <= &2 /\ H / &2 - &1 <= &5 / &12`
  STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["Z"; "H"; "P"; "Q"] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= Q * (&2 - P)` THEN
  SUBGOAL_THEN `Z <= L` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["L"; "H"; "Z"] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= Z * (&5 / &12 - (H / &2 - &1))` THEN
  SUBGOAL_THEN `&0 <= (&5 / &12) * L - Z * (H / &2 - &1)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= (r - (&5 / &12) * b) * L` THEN
  C1092PBO_PROD `&0 <= b * ((&5 / &12) * L - Z * (H / &2 - &1))` THEN
  SUBGOAL_THEN `&0 <= r * L - b * Z * (H / &2 - &1)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= (s - r) * (r * L - b * Z * (H / &2 - &1))` THEN
  SUBGOAL_THEN `c1092pbo_minusPhi b r b r <= c1092pbo_minusPhi c s b r` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   C1092PBO_CANCEL_TAC `c + b:real` THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `&0 <= (s - r) * x`) (concl th))) THEN
   MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 <= x ==> &0 <= y`) THEN
   MAP_EVERY EXPAND_TAC ["L"; "H"; "Z"; "P"; "Q"] THEN REWRITE_TAC[c1092pbo_minusPhi] THEN
   UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `b + r - &2 + r pow 2 + b * c1092pbo_minusPhi b r b r = c1092pbo_endpoint b r`
  ASSUME_TAC THENL
  [REWRITE_TAC[c1092pbo_minusPhi; c1092pbo_endpoint] THEN
   UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092PBO_PROD `&0 <= b * (c1092pbo_minusPhi c s b r - c1092pbo_minusPhi b r b r)` THEN
  REWRITE_TAC[c1092pbo_minusMargin] THEN RASM_ARITH_TAC);;
