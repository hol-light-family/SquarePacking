(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/CornerFloorProfile.lean              *)
(* (N12Compact.C1092MMMPCornerFloorProfile).  A scaled lower corner face     *)
(* supplies the complete directional profile for the top-wall transfer.      *)
(* K = cK sK uK vK aK; profile is C1092WPS_profile; upper_nn/upper_np are    *)
(* C1092WS_*; square_support_bound C1092MPWS_SQUARE_SUPPORT_BOUND;           *)
(* MixedCornerScalars.elementary C1092MCS_ELEMENTARY; centerX is lcx.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCorner.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;

let C1092MCFP_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MCFP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MCFP_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092MCFP_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

let C1092MCFP_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* the quotient (x+y)/(1+x) of the profile *)
let C1092MCFP_KAPPA = prove
 (`forall x y. &0 <= x ==> (&1 + x) * ((x + y) / (&1 + x)) = x + y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC);;

(* Lean: direction_data (private) *)
let C1092MCFP_DIRECTION_DATA = prove
 (`forall x y. &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1
     ==> x <= &1 /\ y <= &1 /\ &1 <= x + y /\
         &1 / &2 + (&9 / &20) * y <= (x + y) / (&1 + x) /\
         y * (&2 - (x + y) / (&1 + x)) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `y:real`] C1092MCFP_KAPPA) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(x + y) / (&1 + x)`,`k:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MCFP_PROD `&0 <= x * y` THEN
  SUBGOAL_THEN `x <= &1 /\ y <= &1 /\ &1 <= x + y` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [NLIN_TAC [SQ_NONNEG `y:real`]; NLIN_TAC [SQ_NONNEG `x:real`];
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCFP_PROD `&0 < (&1 - x - y) * (&1 + x + y)` THEN C1092MCFP_LP_TAC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MCFP_PROD `&0 <= (&3 * y - &2) * (&3 * y - &2)` THEN
  C1092MCFP_PROD `&0 <= y * ((&3 * y - &2) * (&3 * y - &2) + &2 * (x + y - &1))` THEN
  SUBGOAL_THEN `(&1 + x) * (&10 * x - &10 + &11 * y - &9 * x * y) =
                y * ((&3 * y - &2) * (&3 * y - &2) + &2 * (x + y - &1))` ASSUME_TAC THENL
  [UNDISCH_TAC `x * x + y * y = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + x`; `&10 * x - &10 + &11 * y - &9 * x * y`] C1092MCFP_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; DISCH_TAC] THEN
  C1092MCFP_PROD `&0 <= (x * x) * (&1 + x - y)` THEN
  SUBGOAL_THEN `(&1 + y) * (&1 + x - &2 * y - x * y + y * y) = (x * x) * (&1 + x - y)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `x * x + y * y = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + y`; `&1 + x - &2 * y - x * y + y * y`] C1092MCFP_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `y * ((&1 + x) * k) = y * (x + y)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MP_TAC(SPECL [`&1 + x`; `k - (&1 / &2 + (&9 / &20) * y)`] C1092MCFP_CANCEL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; REAL_ARITH_TAC];
   MP_TAC(SPECL [`&1 + x`; `&1 - y * (&2 - k)`] C1092MCFP_CANCEL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; REAL_ARITH_TAC]]);;

(* Lean: face_scalar (private) *)
let C1092MCFP_FACE_SCALAR = prove
 (`forall c s. c977cc_normal c s
     ==> c * (&11 / &4 - (&5 / &4) * (c + s)) <= &1 + (c + s) / &2 - s * (c + s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCS_ELEMENTARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MCFP_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 <= (&2 + c) * (&1 + c) - &9 * c * s` ASSUME_TAC THENL
  [C1092MCFP_LP_TAC; ALL_TAC] THEN
  C1092MCFP_PROD `&0 <= s * ((&2 + c) * (&1 + c) - &9 * c * s)` THEN
  SUBGOAL_THEN `(&1 + c) * (&4 + &2 * (c + s) - &4 * s * (c + s) - &11 * c + &5 * c * (c + s)) =
                s * ((&2 + c) * (&1 + c) - &9 * c * s)` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + c`; `&4 + &2 * (c + s) - &4 * s * (c + s) - &11 * c + &5 * c * (c + s)`]
    C1092MCFP_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; REAL_ARITH_TAC]);;

(* Lean: positive_scalar (private) *)
let C1092MCFP_POSITIVE_SCALAR = prove
 (`forall c s x y. c977cc_normal c s /\ &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1 /\
             &0 <= x * c - y * s
             ==> c * (C1092WPS_profile x y + &2 * y) <=
                 (x * c - y * s) * (c + s) + y * (&1 + (c + s) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `y:real`] C1092MCFP_DIRECTION_DATA) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCFP_FACE_SCALAR) THEN
  ASM_REWRITE_TAC[C1092WPS_profile] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MCFP_NORMAL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MCFP_PROD `&0 <= x * c` THEN C1092MCFP_PROD `&0 <= y * s` THEN
  C1092MCFP_PROD `&0 <= (x * c - y * s) * (x * c + y * s)` THEN
  SUBGOAL_THEN `(x * c - y * s) * (x * c + y * s) = x * x - s * s` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `x * x + y * y = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= x` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MCFP_PROD `&0 < (s - x) * (s + x)` THEN C1092MCFP_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c + s - &1) * (x - (&5 / &4) * y) + (&9 / &20) * y * y` ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= x - (&5 / &4) * y` THENL
   [C1092MCFP_PROD `&0 <= (c + s - &1) * (x - (&5 / &4) * y)` THEN
    C1092MCFP_PROD `&0 <= y * y` THEN C1092MCFP_LP_TAC;
    C1092MCFP_PROD `&0 <= (x - (c + s - &1)) * --(x - (&5 / &4) * y)` THEN
    C1092MCFP_PROD `&0 <= (x - (&5 / &8) * y) * (x - (&5 / &8) * y)` THEN
    C1092MCFP_PROD `&0 <= y * y` THEN C1092MCFP_LP_TAC]; ALL_TAC] THEN
  C1092MCFP_PROD `&0 <= y * ((&1 + (c + s) / &2 - s * (c + s)) -
                             c * (&11 / &4 - (&5 / &4) * (c + s)))` THEN
  C1092MCFP_PROD `&0 <= (c * y) * ((x + y) / (&1 + x) - (&1 / &2 + (&9 / &20) * y))` THEN
  C1092MCFP_PROD `&0 <= c * ((c + s - &1) * (x - (&5 / &4) * y) + (&9 / &20) * y * y)` THEN
  C1092MCFP_LP_TAC);;

(* Lean: support_profile *)
let C1092MCFP_SUPPORT_PROFILE = prove
 (`forall cK sK uK vK aK x y.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ &1 < aK /\ c977cc_normal cK (--sK) /\
     (forall p q. linside cK sK uK vK aK p q ==> --(&1) <= p) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     aK * (cK + --sK) / &2 - --sK <= vK /\
     &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1
     ==> aK * C1092WPS_profile x y - x + &2 * y <= ABT_upper cK sK uK vK aK x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `y:real`] C1092MCFP_DIRECTION_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MCFP_NORMAL_TAC THEN
  SUBGOAL_THEN `aK * (&1 + (cK + --sK) / &2) - --sK <= vK + aK` ASSUME_TAC THENL
  [C1092MCFP_LP_TAC; ALL_TAC] THEN
  C1092MCFP_PROD `&0 <= x * --sK` THEN C1092MCFP_PROD `&0 <= y * cK` THEN
  SUBGOAL_THEN `&0 <= x * --sK + y * cK` ASSUME_TAC THENL [C1092MCFP_LP_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= x * cK - y * --sK` THENL
  [MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `x:real`; `y:real`;
                 `x * cK - y * --sK`; `x * --sK + y * cK`] C1092MCSUP_UPPER_NN) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REAL_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `--(&1)`; `&0`; `&1`]
     C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x':real`; `y':real`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[lcx; lcy; tss_support_radius] THEN
   SUBGOAL_THEN `abs(-- &1 * cK + &0 * sK) = cK /\ abs(-- -- &1 * sK + &0 * cK) = --sK`
   (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `aK * (cK + --sK) - &1 <= cK * (uK + aK) + --sK * (vK + aK)` ASSUME_TAC THENL
   [C1092MCFP_LP_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cK:real`; `--sK:real`; `x:real`; `y:real`] C1092MCFP_POSITIVE_SCALAR) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   C1092MCFP_PROD `&0 <= (x * cK - y * --sK) *
      ((cK * (uK + aK) + --sK * (vK + aK)) - (aK * (cK + --sK) - &1))` THEN
   C1092MCFP_PROD `&0 <= y * ((vK + aK) - (aK * (&1 + (cK + --sK) / &2) - --sK))` THEN
   C1092MCFP_PROD `&0 <= aK * (((x * cK - y * --sK) * (cK + --sK) + y * (&1 + (cK + --sK) / &2)) -
                              cK * (C1092WPS_profile x y + &2 * y))` THEN
   C1092MCFP_PROD `&0 <= (aK - &1) * (cK * y)` THEN
   SUBGOAL_THEN `y * (vK + aK) * (cK * cK + sK * sK) = y * (vK + aK)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o AP_TERM `(*) (cK:real)` o check (fun th ->
     is_eq(concl th) && lhand(concl th) = `ABT_upper cK sK uK vK aK x y`)) THEN
   MP_TAC(SPECL [`cK:real`; `ABT_upper cK sK uK vK aK x y -
                             (aK * C1092WPS_profile x y - x + &2 * y)`] C1092MCFP_CANCEL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; DISCH_TAC THEN RASM_ARITH_TAC];
   SUBGOAL_THEN `x * cK - y * --sK <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `x:real`; `y:real`;
                 `x * cK - y * --sK`; `x * --sK + y * cK`] C1092WS_UPPER_NP) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REAL_ARITH_TAC; DISCH_TAC] THEN
   RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                            else REWRITE_RULE[linside] th) THEN
   SUBGOAL_THEN `uK < --(--sK)` ASSUME_TAC THENL [C1092MCFP_LP_TAC; ALL_TAC] THEN
   C1092MCFP_PROD `&0 <= --(x * cK - y * --sK) * (--(--sK) - uK)` THEN
   C1092MCFP_PROD `&0 <= (x * --sK + y * cK) * ((vK + aK) - (aK * (&1 + (cK + --sK) / &2) - --sK))` THEN
   SUBGOAL_THEN `(x * cK - y * --sK) pow 2 + (x * --sK + y * cK) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cK pow 2 + --sK pow 2 = &1` THEN UNDISCH_TAC `x pow 2 + y pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   ABBREV_TAC `al = x * cK - y * --sK` THEN ABBREV_TAC `be = x * --sK + y * cK` THEN
   ABBREV_TAC `s = --sK` THEN
   SUBGOAL_THEN `--al <= s` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["al"] THEN
    C1092MCFP_PROD `&0 <= (&1 - y) * s` THEN C1092MCFP_PROD `&0 <= x * cK` THEN
    C1092MCFP_LP_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `cK <= be` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCFP_PROD `&0 <= (s + al) * (s - al)` THEN
    C1092MCFP_PROD `&0 < (cK - be) * (cK + be)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MCFP_LP_TAC; ALL_TAC] THEN
   C1092MCFP_PROD `&0 <= s * be` THEN
   C1092MCFP_PROD `&0 <= --al * (s * (&1 + be) - --al)` THEN
   SUBGOAL_THEN `(&1 + be) * (be + s * --al - &1) = --al * (s * (&1 + be) - --al)` ASSUME_TAC THENL
   [UNDISCH_TAC `al pow 2 + be pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPECL [`&1 + be`; `be + s * --al - &1`] C1092MCFP_CANCEL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN C1092MCFP_LP_TAC; DISCH_TAC] THEN
   C1092MCFP_PROD `&0 <= (be - cK) * (&1 + (cK + s) / &2)` THEN
   C1092MCFP_PROD `&0 <= cK * (cK + s - &1)` THEN
   SUBGOAL_THEN `&1 <= be * (&1 + (cK + s) / &2)` ASSUME_TAC THENL
   [C1092MCFP_LP_TAC; ALL_TAC] THEN
   C1092MCFP_PROD `&0 <= be * (cK - s)` THEN
   C1092MCFP_PROD `&0 <= (aK - &1) * (be * (&1 + (cK + s) / &2) - &1)` THEN
   SUBGOAL_THEN `aK <= ABT_upper cK sK uK vK aK x y` ASSUME_TAC THENL
   [C1092MCFP_LP_TAC; ALL_TAC] THEN
   C1092MCFP_PROD `&0 <= y * ((x + y) / (&1 + x))` THEN
   SUBGOAL_THEN `C1092WPS_profile x y <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_profile] THEN C1092MCFP_LP_TAC; ALL_TAC] THEN
   C1092MCFP_PROD `&0 <= (aK - &1) * (&1 - C1092WPS_profile x y)` THEN
   UNDISCH_TAC `&0 <= (aK - &1) * (&1 - C1092WPS_profile x y)` THEN
   REWRITE_TAC[C1092WPS_profile] THEN DISCH_TAC THEN
   C1092MCFP_LP_TAC]);;
