(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveLeftOwnV.lean (Jatloe, N12-jatloe;       *)
(* namespace N12Compact.PositiveLeftOwnV).  The positive left singleton's    *)
(* own transverse separator.  Normal is c977cc_normal; upper/lower are       *)
(* ABT_upper/ABT_lower; F is pccm_f; vertexDefect is pcplb_vertexdefect;     *)
(* upper/lower_in_bands: C977NCO_UPPER/LOWER_IN_BANDS; ThreeSquare.          *)
(* bottom_wall: TSS_BOTTOM_WALL; FourSquareBLBridge.left_wall:              *)
(* FSBL_LEFT_WALL; PositiveCentralCrossMargin.margin / diagonal_minimum:     *)
(* PCCM_MARGIN / PCCM_DIAGONAL_MINIMUM; vertex_bounds: PCPL_VERTEX_BOUNDS;   *)
(* PositiveLeftOwnVBounds.vertex_margin: PLOVB_VERTEX_MARGIN.                *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveCentralCrossMargin.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftBounds.ml";;
needs "n12/geometry/PositiveLeftOwnVBounds.ml";;
needs "n12/geometry/PositiveCentralPositiveLeft.ml";;

let PLOV_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PLOV_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PLOV_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PLOV_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN STRIP_ASSUME_TAC];;

let PLOV_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let PLOV_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* max x 0 in the two band formulas *)
let PLOV_MAX_ABS = prove
 (`forall x. abs x = &2 * max x (&0) - x /\ &0 <= max x (&0) /\ x <= max x (&0)`,
  GEN_TAC THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* the left wall of a contained positive square *)
let PLOV_LEFT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ lcont c s u v a
     ==> &0 <= c * u - s * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  PLOV_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: face_bounds *)
let PLOV_FACE_BOUNDS = prove
 (`forall cO sO uO vO aO cL sL uL vL aL.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ &1 < aO /\ &1 < aL /\
     lcont cO sO uO vO aO /\ uO + aO <= &2 * cO + (&457 / &500) * sO /\
     linside cL sL uL vL aL (&1) (&1) /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL
     ==> pccm_f cO sO cL sL < vL + aL /\ pccm_f cO sO cL sL < &1 + cL - sL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PLOV_NORMAL_TAC THEN
  MP_TAC(SPEC `sO * cL - cO * sL` PLOV_MAX_ABS) THEN STRIP_TAC THEN
  ABBREV_TAC `M = max (sO * cL - cO * sL) (&0)` THEN
  PLOV_PROD_TAC `cO:real` `cL:real` THEN PLOV_PROD_TAC `sO:real` `sL:real` THEN
  SUBGOAL_THEN `ABT_upper cO sO uO vO aO (--sL) cL =
                (sO * cL - cO * sL) * uO + (cO * cL + sO * sL) * vO +
                aO * ((cO * cL + sO * sL) + M)` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
   SUBGOAL_THEN `--sL * cO + cL * sO = sO * cL - cO * sL /\
                 --(--sL) * sO + cL * cO = cO * cL + sO * sL` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(cO * cL + sO * sL) = cO * cL + sO * sL` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcy] THEN
  SUBGOAL_THEN `abs sO = sO` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cO * vO + sO * uO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cO * (pccm_f cO sO cL sL - &1) =
                --sL * (&2 * cO + (&457 / &500) * sO) + sL + cO * ((cO * cL + sO * sL) + M)`
    ASSUME_TAC THENL
  [REWRITE_TAC[pccm_f] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~(cO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `cO * (ABT_upper cO sO uO vO aO (--sL) cL - (pccm_f cO sO cL sL - &1)) =
    (cO * cL + sO * sL) * (cO * vO + sO * uO) +
    sL * (&2 * cO + (&457 / &500) * sO - (uO + aO)) +
    (aO - &1) * (sL + cO * ((cO * cL + sO * sL) + M))` ASSUME_TAC THENL
  [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
     filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PLOV_PROD_TAC `cO * cL + sO * sL` `cO * vO + sO * uO` THEN
  PLOV_PROD_TAC `sL:real` `&2 * cO + (&457 / &500) * sO - (uO + aO)` THEN
  PLOV_PROD_TAC `cO:real` `(cO * cL + sO * sL) + M` THEN
  PLOV_PRODLT_TAC `cO:real` `cL:real` THEN
  SUBGOAL_THEN `&0 < sL + cO * ((cO * cL + sO * sL) + M)` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  PLOV_PRODLT_TAC `aO - &1` `sL + cO * ((cO * cL + sO * sL) + M)` THEN
  SUBGOAL_THEN `pccm_f cO sO cL sL - &1 < ABT_upper cO sO uO vO aO (--sL) cL`
    ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PLOV_POS_OF_MUL THEN
   EXISTS_TAC `cO:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cL sL uL vL aL (&1) (&1)`) THEN REWRITE_TAC[linside] THEN
  STRIP_TAC THEN CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: lower_face (private) *)
let PLOV_LOWER_FACE = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r
     ==> &2 * l - &2 * r <= pccm_f p q l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PLOV_USE PCCM_DIAGONAL_MINIMUM [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PLOV_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= r * (&1 - (&457 / &500) * r) / l` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_DIV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: central_margin *)
let PLOV_CENTRAL_MARGIN = prove
 (`forall p q C S l r.
     c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal l r /\
     pccm_f p q l r <= &1 + l - r
     ==> l * (&2 * (C + S) - &1) <=
         S * pccm_f p q l r + l * (C * l + S * r + max (C * r - S * l) (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PLOV_USE PCCM_MARGIN [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PLOV_USE PLOV_LOWER_FACE [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PLOV_USE C977CSB_DOT_LE_ONE [`l:real`; `r:real`; `C:real`; `S:real`] THEN
  PLOV_NORMAL_TAC THEN
  ABBREV_TAC `FF = pccm_f p q l r` THEN
  ASM_CASES_TAC `S <= r` THENL
  [PLOV_USE C977CSB_COSINE_ORDER [`l:real`; `r:real`; `C:real`; `S:real`] THEN
   PLOV_PROD_TAC `r:real` `C - l` THEN PLOV_PROD_TAC `l:real` `r - S` THEN
   SUBGOAL_THEN `max (C * r - S * l) (&0) = C * r - S * l` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `y <= x ==> max x y = x`) THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
   PLOV_PROD_TAC `l:real` `&1 + l - r - FF` THEN PLOV_PROD_TAC `l:real` `l - r` THEN
   PLOV_PROD_TAC `l:real` `&2 - l - r` THEN
   SUBGOAL_THEN `(l * (&2 - l - r)) * r - (l * (&2 + l - r) - FF) * l =
                 l * (FF + &2 * r - &2 * l - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPECL [`l:real`; `r:real`; `C:real`; `S:real`; `l * (&2 - l - r)`;
                 `l * (&2 + l - r) - FF`] C977CSB_LINEAR_ARC_MAX) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC ORELSE NLIN_TAC ~deg2:false []);
                   DISCH_TAC] THEN
   SUBGOAL_THEN `l - (l * (&2 - l - r)) * l - (l * (&2 + l - r) - FF) * r =
                 r * FF - &2 * l * (l + r - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PLOV_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `l:real`; `r:real`] THEN
  PLOV_PROD_TAC `r:real` `l - C` THEN PLOV_PROD_TAC `l:real` `S - r` THEN
  SUBGOAL_THEN `max (C * r - S * l) (&0) = &0` SUBST1_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `x <= y ==> max x y = y`) THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PLOV_PROD_TAC `l:real` `&2 - l` THEN
  PLOV_PROD_TAC `l:real` `FF - (&2 * l - &2 * r)` THEN
  SUBGOAL_THEN `&0 <= (l * (&2 - l)) * r - (&2 * l - l * r - FF) * l` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PLOV_PROD_TAC `l * (&2 - l)` `&1 - (l * C + r * S)` THEN
  PLOV_PROD_TAC `(l * (&2 - l)) * r - (&2 * l - l * r - FF) * l` `S - r` THEN
  SUBGOAL_THEN
   `l * (((l * (&2 - l)) * l + (&2 * l - l * r - FF) * r) -
         ((l * (&2 - l)) * C + (&2 * l - l * r - FF) * S)) =
    (l * (&2 - l)) * (&1 - l * C - r * S) +
    ((l * (&2 - l)) * r - (&2 * l - l * r - FF) * l) * (S - r)` ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((l * (&2 - l)) * l + (&2 * l - l * r - FF) * r) -
                      ((l * (&2 - l)) * C + (&2 * l - l * r - FF) * S)` ASSUME_TAC THENL
  [MATCH_MP_TAC PLOV_NONNEG_OF_MUL THEN EXISTS_TAC `l:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `l - (l * (&2 - l)) * l - (&2 * l - l * r - FF) * r =
                r * FF - &2 * l * (l + r - &1)` ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_axis_impossible *)
let PLOV_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cA sA uA (vA:real) aA.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cA sA /\
     aO = aL /\ aL = aA /\ &1 < aA /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     linside cL sL uL vL aL (&1) (&1) /\ uA + aA <= &2 * (cA + sA) /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL
     ==> ~(ABT_upper cL sL uL vL aL cA sA <= uA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  PLOV_USE PLOV_FACE_BOUNDS [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PLOV_USE PLOV_LEFT_WALL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PLOV_USE PLOV_CENTRAL_MARGIN [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `cL:real`; `sL:real`] THEN
  PLOV_NORMAL_TAC THEN
  MP_TAC(SPEC `sA * cL - cA * sL` PLOV_MAX_ABS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `max (cA * sL - sA * cL) (&0) = max (sA * cL - cA * sL) (&0) - (sA * cL - cA * sL)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [REWRITE_TAC[real_max] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
                      ALL_TAC] THEN
  ABBREV_TAC `M = max (sA * cL - cA * sL) (&0)` THEN
  PLOV_PROD_TAC `cA:real` `cL:real` THEN PLOV_PROD_TAC `sA:real` `sL:real` THEN
  SUBGOAL_THEN `ABT_upper cL sL uL vL aL cA sA =
                (cA * cL + sA * sL) * (uL + aL) + (sA * cL - cA * sL) * vL + aL * M`
    ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
   SUBGOAL_THEN `cA * cL + sA * sL = cA * cL + sA * sL /\
                 --cA * sL + sA * cL = sA * cL - cA * sL` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(cA * cL + sA * sL) = cA * cL + sA * sL` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `cL * ABT_upper cL sL uL vL aL cA sA - sA * (vL + aL) -
    aL * cL * ((cA * cL + sA * sL) + (M - (sA * cL - cA * sL))) =
    (cA * cL + sA * sL) * (cL * uL - sL * (vL + aL))` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cL pow 2 + sL pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PLOV_PROD_TAC `cA * cL + sA * sL` `cL * uL - sL * (vL + aL)` THEN
  PLOV_PROD_TAC `sA:real` `(vL + aL) - pccm_f cO sO cL sL` THEN
  PLOV_PROD_TAC `cL:real` `(cA * cL + sA * sL) + (M - (sA * cL - cA * sL))` THEN
  PLOV_PROD_TAC `cL * ((cA * cL + sA * sL) + (M - (sA * cL - cA * sL)))` `aL - &1` THEN
  PLOV_PRODLT_TAC `cL:real` `&2 * (cA + sA) - &1 - uA` THEN
  PLOV_PROD_TAC `cL:real` `uA - ABT_upper cL sL uL vL aL cA sA` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: vertex_closed (private) *)
let PLOV_VERTEX_CLOSED = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> lclosed c s u v a (c * u - s * (v + a)) (s * u + c * (v + a))`,
  ACCEPT_TAC PCPL_VERTEX_CLOSED);;

(* Lean: own_axis_impossible *)
let PLOV_OWN_AXIS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cA sA uA vA aA.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cA sA /\
     &1 < aO /\ &1 < aL /\ &1 < aA /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     linside cL sL uL vL aL (&1) (&1) /\
     sO <= sA /\ &9 / &10 <= cO /\ &4 / &5 <= cA /\ sA <= &3 / &5 /\
     uA + aA <= &2 * (cA + sA) /\ vA + aA <= &2 * cA - sA /\
     &1 + (cA + sA) * (&1 - &2 * sA) + cA * (&1 - cO) < cA * (vA + aA) /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL
     ==> ~(uL + aL <= ABT_lower cA sA uA vA aA cL sL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  PLOV_USE PLOV_FACE_BOUNDS [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PLOV_USE PLOV_LEFT_WALL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PLOV_NORMAL_TAC THEN
  PLOV_PROD_TAC `sL:real` `(vL + aL) - pccm_f cO sO cL sL` THEN
  PLOV_PRODLT_TAC `cL:real` `aL - &1` THEN
  SUBGOAL_THEN `cL + sL * pccm_f cO sO cL sL < cL * (uL + aL)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `sA <= sL` THENL
  [PLOV_USE C977CSB_COSINE_ORDER [`cL:real`; `sL:real`; `cA:real`; `sA:real`] THEN
   PLOV_PROD_TAC `cA:real` `cL:real` THEN PLOV_PROD_TAC `sA:real` `sL:real` THEN
   PLOV_PROD_TAC `sL:real` `cA - cL` THEN PLOV_PROD_TAC `cL:real` `sL - sA` THEN
   SUBGOAL_THEN `&0 <= cA * sL - sA * cL` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   SUBGOAL_THEN `ABT_lower cA sA uA vA aA cL sL =
                 (cA * cL + sA * sL) * uA + (cA * sL - sA * cL) * vA` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `cL * cA + sL * sA = cA * cL + sA * sL /\
                  --cL * sA + sL * cA = cA * sL - sA * cL` (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(cA * cL + sA * sL) = cA * cL + sA * sL /\
                  abs(cA * sL - sA * cL) = cA * sL - sA * cL`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[REAL_ABS_REFL] THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   PLOV_PROD_TAC `cL + cA - &1` `&1 - sA` THEN
   PLOV_PROD_TAC `cA * sL - sA * cL` `(cL + cA - &1) * (&1 - sA) + (&1 - sL)` THEN
   SUBGOAL_THEN `(cL + cA) * ((cA * cL + sA * sL) + (&1 - sA) * (cA * sL - sA * cL) - &1) =
                 (cA * sL - sA * cL) * ((cL + cA - &1) * (&1 - sA) + (&1 - sL))`
     ASSUME_TAC THENL
   [UNDISCH_TAC `cL pow 2 + sL pow 2 = &1` THEN UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (cA * cL + sA * sL) + (&1 - sA) * (cA * sL - sA * cL) - &1`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PLOV_NONNEG_OF_MUL THEN EXISTS_TAC `cL + cA` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   PLOV_PROD_TAC `cA * cL + sA * sL` `&2 * (cA + sA) - (uA + aA)` THEN
   PLOV_PROD_TAC `cA * sL - sA * cL` `&2 * cA - sA - (vA + aA)` THEN
   PLOV_PROD_TAC `(cA * cL + sA * sL) + (cA * sL - sA * cL)` `aA - &1` THEN
   SUBGOAL_THEN
    `(cA * cL + sA * sL) * (&2 * (cA + sA) - aA) + (cA * sL - sA * cL) * (&2 * cA - sA - aA) =
     &2 * (cL + sL) + sA * (cA * sL - sA * cL) -
     aA * ((cA * cL + sA * sL) + (cA * sL - sA * cL))` ASSUME_TAC THENL
   [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `ABT_lower cA sA uA vA aA cL sL <= &2 * (cL + sL) - &1` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PLOV_USE PCCM_MARGIN [`cO:real`; `sO:real`; `cL:real`; `sL:real`] THEN
   PLOV_PROD_TAC `cL:real` `(&2 * (cL + sL) - &1) - (uL + aL)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PLOV_USE PCPL_VERTEX_BOUNDS [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cO:real`] THEN
  PLOV_USE PLOV_VERTEX_CLOSED [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PLOV_USE ABT_CLOSED_BOUNDS [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `cA * uA - sA * (vA + aA)`; `sA * uA + cA * (vA + aA)`; `cL:real`; `sL:real`] THEN
  PLOV_USE PLOVB_VERTEX_MARGIN [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `cL:real`; `sL:real`] THEN
  PLOV_PRODLT_TAC `cL:real` `cL:real` THEN
  PLOV_PRODLT_TAC `cL * cL`
    `(&1 - (pcplb_vertexdefect cA sA + sA * (&1 - cO))) - (cA * uA - sA * (vA + aA))` THEN
  PLOV_PROD_TAC `cL:real` `sL:real` THEN
  PLOV_PROD_TAC `cL * sL` `(&2 - sA * (&1 - cA)) - (sA * uA + cA * (vA + aA))` THEN
  PLOV_PROD_TAC `cL:real`
    `(cL * (cA * uA - sA * (vA + aA)) + sL * (sA * uA + cA * (vA + aA))) -
     ABT_lower cA sA uA vA aA cL sL` THEN
  PLOV_PROD_TAC `cL:real` `ABT_lower cA sA uA vA aA cL sL - (uL + aL)` THEN
  NLIN_TAC ~deg2:false []);;
