(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveLeftOwnVEndpoint.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.PositiveLeftOwnVEndpoint).               *)
(* The central-equals-left endpoint of the genuine own-V entrance.           *)
(* Normal is c977cc_normal; vertexDefect is pcplb_vertexdefect; F is pccm_f. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftBounds.ml";;
needs "n12/geometry/PositiveCentralCrossMargin.ml";;

let PLOVE_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PLOVE_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

(* Lean: endpoint_left *)
let PLOVE_ENDPOINT_LEFT = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r /\ &9 / &10 <= p /\ q <= r
     ==> l pow 2 * (&1 - pcplb_vertexdefect l r - r * (&1 - p)) +
         l * r * (&2 - r * (&1 - l)) <= l + r * pccm_f p q l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `p:real`; `q:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN PLOVE_NORMAL_TAC THEN
  PLOVE_PROD_TAC `l:real` `r - q` THEN PLOVE_PROD_TAC `r:real` `p - l` THEN
  SUBGOAL_THEN `max (q * l - p * r) (&0) = &0` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `x <= y ==> max x y = y`) THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[pccm_f; pcplb_vertexdefect; REAL_ADD_RID] THEN
  SUBGOAL_THEN `forall x. x / p = x * inv p` (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[real_div]; ALL_TAC] THEN
  SUBGOAL_THEN `forall x. x / l = x * inv l` (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[real_div]; ALL_TAC] THEN
  SUBGOAL_THEN `p * inv p = &1 /\ l * inv l = &1 /\ &0 < inv p` MP_TAC THENL
  [REPEAT CONJ_TAC THEN
   FIRST [MATCH_MP_TAC REAL_MUL_RINV; MATCH_MP_TAC REAL_LT_INV] THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `ip = inv p` THEN ABBREV_TAC `il = inv l` THEN STRIP_TAC THEN
  (* the bracket *)
  SUBGOAL_THEN `p * l <= &1` ASSUME_TAC THENL
  [PLOVE_PROD_TAC `l:real` `&1 - p` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PLOVE_PROD_TAC `&1 - p * l` `&1 - l` THEN
  SUBGOAL_THEN `p * l * (&1 - l) <= r` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= r * ((&1 - p) + q * (p - &457 / &500)) - p * (&1 - p) * l * (&1 - l)`
   ASSUME_TAC THENL
  [ASM_CASES_TAC `&457 / &500 <= p` THENL
   [PLOVE_PROD_TAC `&1 - p` `r - p * l * (&1 - l)` THEN
    PLOVE_PROD_TAC `r:real` `q:real` THEN
    PLOVE_PROD_TAC `r * q` `p - &457 / &500` THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
   SUBGOAL_THEN `&2 / &5 <= q` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    PLOVE_PROD_TAC `&457 / &500 - p` `&457 / &500 + p` THEN
    PLOVE_PROD_TAC `&2 / &5 - q` `&2 / &5 + q` THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PLOVE_PROD_TAC `l:real` `&1 - l` THEN
   PLOVE_PROD_TAC `&1 - p` `l * (&1 - l)` THEN
   SUBGOAL_THEN `p * l * (&1 - l) <= &1 / &4` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [SQ_NONNEG `l - &1 / &2`]; ALL_TAC] THEN
   PLOVE_PROD_TAC `(&1 - p) - &43 / &500` `r - p * l * (&1 - l)` THEN
   PLOVE_PROD_TAC `r:real` `q:real` THEN
   PLOVE_PROD_TAC `r:real` `r - q` THEN
   PLOVE_PROD_TAC `l - r` `l + r` THEN
   SUBGOAL_THEN `r * q <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PLOVE_PROD_TAC `r * q` `&7 / &500 - (&457 / &500 - p)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PLOVE_PROD_TAC `ip:real` `r:real` THEN
  PLOVE_PROD_TAC `ip * r`
   `r * ((&1 - p) + q * (p - &457 / &500)) - p * (&1 - p) * l * (&1 - l)` THEN
  (* the base term *)
  PLOVE_PROD_TAC `r:real` `&1 - r` THEN
  SUBGOAL_THEN `&0 <= l * (&1 + l) - (&1 - r)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PLOVE_PROD_TAC `(&1 - l) pow 2` `l * (&1 + l) - (&1 - r)` THEN
  SUBGOAL_THEN
   `(l + r * (&1 - &2 * r - &457 / &500 * q * r * ip + r * ip + (p * l + q * r))) -
    (l pow 2 * (&1 - (&1 - l) * (&1 - r) * il - r * (&1 - p)) +
     l * r * (&2 - r * (&1 - l))) =
    (&1 - l) pow 2 * (l * (&1 + l) - (&1 - r)) +
    ip * r * (r * ((&1 - p) + q * (p - &457 / &500)) - p * (&1 - p) * l * (&1 - l))`
   ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN UNDISCH_TAC `l * il = &1` THEN
   UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;
