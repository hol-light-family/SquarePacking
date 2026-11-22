(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardSmallThreeBottomScalars.lean   *)
(* (N12Compact.C1092MPPMInwardSmallThree).  The actual bottom-square tilt    *)
(* bound in SMALL-INWARD-THREE-SQUARE-ENDING section 3.  Normal:             *)
(* c977cc_normal (normal_bounds: C977CC_NORMAL_BOUNDS); half: C1092WPS_half; *)
(* small_bounds: C1092ISTS_SMALL_BOUNDS; J0, Q: c1092ists_J0, c1092ists_Q.   *)
(* Tag C1092ISTB_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeData.ml";;

let C1092ISTB_LIN = NLIN_TAC ~deg2:false [];;
let C1092ISTB_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ISTB_LIN; ALL_TAC];;
(* keep only the listed assumptions *)
let C1092ISTB_KEEP_TAC tms =
  POP_ASSUM_LIST(fun ths -> MAP_EVERY ASSUME_TAC
    (filter (fun th -> exists (aconv (concl th)) tms) (rev ths)));;
let C1092ISTB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: positive_source_margin *)
let C1092ISTB_POSITIVE_SOURCE_MARGIN = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k /\ C1092WPS_half c s <= &53 / &500
     ==> &0 < h * (c pow 2 / &2 + s) + k * (c - c * s / &2 - &543 / &500)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ISTS_SMALL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092ISTB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c pow 2 / &2 + s` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - &7 / &10`]; ALL_TAC] THEN
  C1092ISTB_PROD `&0 < c * (c - s - &19 / &25)` THEN
  SUBGOAL_THEN `&0 < (c pow 2 / &2 + s) + (c - c * s / &2 - &543 / &500)` ASSUME_TAC THENL
   [C1092ISTB_LIN; ALL_TAC] THEN
  C1092ISTB_PROD `&0 <= (h - k) * (c pow 2 / &2 + s)` THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN C1092ISTB_LIN;
    SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
     [UNDISCH_TAC `~(k = &0)` THEN UNDISCH_TAC `&0 <= k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092ISTB_PROD `&0 < k * ((c pow 2 / &2 + s) + (c - c * s / &2 - &543 / &500))` THEN
    C1092ISTB_LIN]);;

(* Lean: positive_tilt *)
let C1092ISTB_POSITIVE_TILT = prove
 (`forall c s h k. c977cc_normal c s /\ c977cc_normal h k /\ C1092WPS_half c s <= &53 / &500 /\
     c1092ists_J0 c s < &0 /\ --c1092ists_J0 c s <= s pow 2 / &10 /\
     h * c1092ists_J0 c s + (&1 - h) pow 2 / &2 +
       k * (h / &2 + c - s - c pow 2 + (&2 / &5) * c * s) < &0
     ==> k < &21 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ISTS_SMALL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092ISTB_NORMAL_TAC THEN
  C1092ISTB_PROD `&0 <= c * (&1 - c)` THEN
  C1092ISTB_PROD `&0 <= s * ((&153 / &250) - (&1 - (&2 / &5) * c))` THEN
  SUBGOAL_THEN `--(&13 / &100) < c - s - c pow 2 + (&2 / &5) * c * s` ASSUME_TAC THENL
   [C1092ISTB_LIN; ALL_TAC] THEN
  C1092ISTB_PROD `&0 <= k * (h / &2 + c - s - c pow 2 + (&2 / &5) * c * s - &11 / &50)` THEN
  C1092ISTB_PROD `&0 <= (&1 - h) * --c1092ists_J0 c s` THEN
  C1092ISTB_PROD `&0 < (&21 / &100 - s) * (&21 / &100 + s)` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - h`]);;

(* Lean: negative_tilt *)
let C1092ISTB_NEGATIVE_TILT =
  let lam = `c * h + s * l` and gam = `s * h - c * l` in
  let ins tm = vsubst [lam, `LAM:real`; gam, `GAM:real`] tm in
  prove
 (`forall c s h l. c977cc_normal c s /\ c977cc_normal h l /\ &0 < s /\ &0 < s * h - c * l /\
     c * h + s * l + c1092ists_Q c s * (s * h - c * l) < &1
     ==> l < s / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ISTB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [C1092ISTB_LIN; ALL_TAC] THEN
  SUBGOAL_THEN (ins `&0 < LAM`) ASSUME_TAC THENL
   [C1092ISTB_PROD `&0 < c * h` THEN C1092ISTB_PROD `&0 <= s * l` THEN C1092ISTB_LIN; ALL_TAC] THEN
  SUBGOAL_THEN (ins `LAM pow 2 + GAM pow 2 = &1`) ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `h pow 2 + l pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092ISTB_PROD (ins `&0 < (&1 - LAM - c1092ists_Q c s * GAM) * (&1 + LAM)`) THEN
  SUBGOAL_THEN (ins `&0 < GAM * (GAM - c1092ists_Q c s * (&1 + LAM))`) ASSUME_TAC THENL
   [C1092ISTB_LIN; ALL_TAC] THEN
  SUBGOAL_THEN (ins `&0 < GAM - c1092ists_Q c s * (&1 + LAM)`) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092ISTB_PROD (ins `&0 <= GAM * --(GAM - c1092ists_Q c s * (&1 + LAM))`) THEN
    C1092ISTB_LIN; ALL_TAC] THEN
  C1092ISTB_PROD `&0 <= (&1 - c) * (c - (&2 / &5) * s)` THEN
  SUBGOAL_THEN `(&2 / &5) * s <= c * c1092ists_Q c s` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ists_Q] THEN C1092ISTB_LIN; ALL_TAC] THEN
  C1092ISTB_PROD (ins `&0 <= (c * c1092ists_Q c s - (&2 / &5) * s) * (&1 + LAM)`) THEN
  C1092ISTB_PROD (ins `&0 < c * (GAM - c1092ists_Q c s * (&1 + LAM))`) THEN
  SUBGOAL_THEN (ins `&0 < c * GAM - (&2 / &5) * s * (&1 + LAM)`) ASSUME_TAC THENL
   [C1092ISTB_LIN; ALL_TAC] THEN
  C1092ISTB_PROD `&0 <= (&1 - c) * (&1 - (&1 / &5) * (&1 + c))` THEN
  C1092ISTB_PROD `&0 <= c * (&1 - h)` THEN
  SUBGOAL_THEN `&0 <= &1 - c * h - s pow 2 / &5` ASSUME_TAC THENL [C1092ISTB_LIN; ALL_TAC] THEN
  C1092ISTB_PROD `&0 <= s * (&1 - c * h - s pow 2 / &5)` THEN
  SUBGOAL_THEN (ins `(c pow 2 + (&2 / &5) * s pow 2) * (s / &5 - l) =
      c * GAM - (&2 / &5) * s * (&1 + LAM) + (&3 / &5) * s * (&1 - c * h - s pow 2 / &5)`) ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c pow 2 + (&2 / &5) * s pow 2) * (s / &5 - l)` ASSUME_TAC THENL
   [C1092ISTB_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092ISTB_PROD `&0 <= (c pow 2 + (&2 / &5) * s pow 2) * (l - s / &5)` THEN
  C1092ISTB_LIN);;
