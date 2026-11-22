(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeSignedPositiveBottom.lean         *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(* N12Compact.CentralNegativeSignedPositiveBottom).                          *)
(* The negative incoming central arc is controlled by three support          *)
(* directions.  Lean lower is ABT_lower; Normal is c977cc_normal;            *)
(* positive_frame_wall_bounds is used through TSS_BOTTOM_WALL.               *)
(* CentralNegativePositiveBottom.impossible: CNPB_IMPOSSIBLE;                *)
(* PositiveBottomWallNeighborAxis.of_entry: PBWNA_OF_ENTRY.                  *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/CentralNegativePositiveBottom.ml";;
needs "n12/geometry/PositiveBottomWallNeighborAxis.ml";;

let CNSPB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CNSPB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let CNSPB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CNSPB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* lower_in_bands, written with the two face coefficients *)
let CNSPB_LOWER_GEN = prove
 (`forall c s u v a nx ny.
     ABT_lower c s u v a nx ny =
     (nx * c + ny * s) * u + (--nx * s + ny * c) * v +
     a / &2 * ((nx * c + ny * s) - abs(nx * c + ny * s)) +
     a / &2 * ((--nx * s + ny * c) - abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

let CNSPB_LOWER_SIGNS = prove
 (`forall c s u v a nx ny k h.
     nx * c + ny * s = k /\ --nx * s + ny * c = h
     ==> (&0 <= k /\ &0 <= h ==> ABT_lower c s u v a nx ny = k * u + h * v) /\
         (&0 <= k /\ h <= &0 ==> ABT_lower c s u v a nx ny = k * u + h * (v + a)) /\
         (k <= &0 /\ &0 <= h ==> ABT_lower c s u v a nx ny = k * (u + a) + h * v) /\
         (k <= &0 /\ h <= &0 ==> ABT_lower c s u v a nx ny = k * (u + a) + h * (v + a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CNSPB_LOWER_GEN] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

(* Lean: diagonal_margin (private) *)
let CNSPB_DIAGONAL_MARGIN = prove
 (`forall c t d r. c977cc_normal c t /\ c977cc_normal d r
     ==> d * ((d - r) * (&2 * c + &3 * t - &1) + (--r * c - d * t) * (&2 * c + &1 / &2)) -
         (c + t) * (d - &2 * d * r - (&457 / &500) * r pow 2) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CNSPB_NORMAL_TAC THEN
  CNSPB_PROD_TAC `t:real` `(&3 / &2) * c - &1` THEN
  CNSPB_PROD_TAC `c - t` `&1 - t / &2` THEN
  SUBGOAL_THEN `c + (&3 / &2) * t - &1 - &2 * c * t <= &0` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  CNSPB_PROD_TAC `c - t` `c + t - &1 / &4` THEN
  SUBGOAL_THEN `&1 - t - c / &2 - &2 * c pow 2 <= --(&3 / &4) * (c + t)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNSPB_PROD_TAC `&1 - d` `(&3 / &5) * d - &2 / &5` THEN
  SUBGOAL_THEN `(&2 / &5) * r pow 2 <= d * (&1 - d)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNSPB_PROD_TAC `d pow 2` `--(c + (&3 / &2) * t - &1 - &2 * c * t)` THEN
  CNSPB_PROD_TAC `c + t` `d * (&1 - d) - (&2 / &5) * r pow 2` THEN
  CNSPB_PROD_TAC `d:real` `r:real` THEN
  CNSPB_PROD_TAC `d * r` `--(&3 / &4) * (c + t) - (&1 - t - c / &2 - &2 * c pow 2)` THEN
  CNSPB_PROD_TAC `r:real` `d - r` THEN
  SUBGOAL_THEN `&0 <= (&3 / &4) * d * r - (&257 / &500) * r pow 2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `r:real`]; ALL_TAC] THEN
  CNSPB_PROD_TAC `c + t` `(&3 / &4) * d * r - (&257 / &500) * r pow 2` THEN
  SUBGOAL_THEN
   `d * ((d - r) * (&2 * c + &3 * t - &1) + (--r * c - d * t) * (&2 * c + &1 / &2)) -
    (c + t) * (d - &2 * d * r - (&457 / &500) * r pow 2) =
    d pow 2 * (c + (&3 / &2) * t - &1 - &2 * c * t) + (d pow 2 - d) * (c + t) +
    d * r * (&1 - t - c / &2 - &2 * c pow 2) + (&457 / &500) * r pow 2 * (c + t)`
   ASSUME_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

let CNSPB_SIGNS_TAC sq nx ny k h n =
  MP_TAC(SPECL (sq @ [nx; ny; k; h]) CNSPB_LOWER_SIGNS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o el n o CONJUNCTS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CNSPB_SUBST_LOWER_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else failwith ""));;

(* Lean: diagonal_impossible *)
let CNSPB_DIAGONAL_IMPOSSIBLE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB t.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cB t /\ c977cc_normal cD sD /\ sB = --t /\
     &1 < aB /\ &1 <= aD /\
     lcont cD sD uD vD aD /\ linside cD sD uD vD aD (&2) (&457 / &500) /\
     vB + aB <= &2 * cB + &3 * t /\
     &1 / &2 < ABT_lower cB sB uB vB aB (&1) (--(&1)) /\
     vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  CNSPB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sD = sD` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cD sD uD vD aD (&2) (&457 / &500)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  CNSPB_PROD_TAC `sD:real` `&2 * cD + (&457 / &500) * sD - uD` THEN
  CNSPB_PROD_TAC `cD:real` `aD - &1` THEN
  SUBGOAL_THEN `cD - &2 * cD * sD - (&457 / &500) * sD pow 2 <= cD * (vD + aD)`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNSPB_PROD_TAC `sD:real` `cB:real` THEN CNSPB_PROD_TAC `cD:real` `t:real` THEN
  CNSPB_PROD_TAC `cB:real` `cD - sD` THEN CNSPB_PROD_TAC `sD:real` `cB - t` THEN
  CNSPB_PROD_TAC `cB - t` `cB + t` THEN CNSPB_PROD_TAC `cD:real` `cB:real` THEN
  SUBGOAL_THEN `&0 <= &2 * cB pow 2 - &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNSPB_PROD_TAC `sD:real` `&2 * cB pow 2 - &1` THEN
  CNSPB_PROD_TAC `cD * cB` `t:real` THEN
  SUBGOAL_THEN `&0 < (cD - sD) - (--sD * cB - cD * t) * (&2 * cB)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  let sqB = [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`] in
  CNSPB_SIGNS_TAC sqB `&1` `--(&1)` `cB + t` `t - cB` 1 THEN
  CNSPB_SIGNS_TAC sqB `--sD` `cD:real` `--sD * cB - cD * t` `cD * cB - sD * t` 2 THEN
  CNSPB_SUBST_LOWER_TAC THEN
  CNSPB_PROD_TAC `--(--sD * cB - cD * t)` `((cB + t) * uB + (t - cB) * (vB + aB)) - &1 / &2` THEN
  CNSPB_PROD_TAC `cB + t` `((--sD * cB - cD * t) * (uB + aB) + (cD * cB - sD * t) * vB) - (vD + aD)` THEN
  CNSPB_PROD_TAC `cD - sD` `(&2 * cB + &3 * t) - (vB + aB)` THEN
  CNSPB_PRODLT_TAC `aB - &1` `(cD - sD) - (--sD * cB - cD * t) * (&2 * cB)` THEN
  SUBGOAL_THEN
   `--(--sD * cB - cD * t) * ((cB + t) * uB + (t - cB) * (vB + aB)) +
    (cB + t) * ((--sD * cB - cD * t) * (uB + aB) + (cD * cB - sD * t) * vB) =
    (cD - sD) * vB + (--sD * cB - cD * t) * (&2 * cB) * aB` ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (cD - sD) * (&2 * cB + &3 * t - &1) + (--sD * cB - cD * t) * (&2 * cB) +
         (--sD * cB - cD * t) / &2 - (cB + t) * (vD + aD)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNSPB_PRODLT_TAC `cD:real`
   `(cD - sD) * (&2 * cB + &3 * t - &1) + (--sD * cB - cD * t) * (&2 * cB) +
    (--sD * cB - cD * t) / &2 - (cB + t) * (vD + aD)` THEN
  CNSPB_PROD_TAC `cB + t` `cD * (vD + aD) - (cD - &2 * cD * sD - (&457 / &500) * sD pow 2)` THEN
  CNSPB_USE CNSPB_DIAGONAL_MARGIN [`cB:real`; `t:real`; `cD:real`; `sD:real`] THEN
  NLIN_TAC ~deg2:false []);;

let CNSPB_NONPOS_OF_MUL = prove
 (`forall k y. &0 < k /\ k * y <= &0 ==> y <= &0`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: endpoint_bound *)
let CNSPB_ENDPOINT_BOUND = prove
 (`forall cB sB uB vB aB t C S.
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal C S /\ c977cc_normal cB t /\ sB = --t /\
     ABT_lower cB sB uB vB aB (&1) (&0) <= &2 /\
     uB <= &2 * cB - (&3 / &2) * t /\
     ABT_lower cB sB uB vB aB (&1) (--(&1)) <= &1 / &2
     ==> ABT_lower cB sB uB vB aB C (--S) <= &2 * C - (&3 / &2) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  CNSPB_NORMAL_TAC THEN
  let sqB = [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`] in
  CNSPB_SIGNS_TAC sqB `&1` `&0` `cB:real` `t:real` 0 THEN
  CNSPB_SIGNS_TAC sqB `&1` `--(&1)` `cB + t` `t - cB` 1 THEN
  CNSPB_PROD_TAC `C:real` `cB:real` THEN CNSPB_PROD_TAC `S:real` `t:real` THEN
  CNSPB_PROD_TAC `cB:real` `C - S` THEN
  ASM_CASES_TAC `&0 <= C * t - S * cB` THENL
  [CNSPB_SIGNS_TAC sqB `C:real` `--S` `C * cB + S * t` `C * t - S * cB` 0 THEN
   CNSPB_SUBST_LOWER_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `&0 < t` THENL
   [CNSPB_PROD_TAC `C * t - S * cB` `&2 - (cB * uB + t * vB)` THEN
    CNSPB_PROD_TAC `S:real` `(&2 * cB - (&3 / &2) * t) - uB` THEN
    SUBGOAL_THEN `t * ((C * cB + S * t) * uB + (C * t - S * cB) * vB) =
                  (C * t - S * cB) * (cB * uB + t * vB) + S * uB` ASSUME_TAC THENL
    [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC[REAL_NEG_GE0] THEN
    MATCH_MP_TAC CNSPB_NONPOS_OF_MUL THEN EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `S = &0` SUBST_ALL_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `S <= &0 /\ &0 <= S ==> S = &0`) THEN
     CONJ_TAC THENL [NLIN_TAC []; RASM_ARITH_TAC]; ALL_TAC] THEN
    CNSPB_PROD_TAC `C:real` `&2 - (cB * uB + &0 * vB)` THEN
    NLIN_TAC ~deg2:false []];
   ALL_TAC] THEN
  CNSPB_SIGNS_TAC sqB `C:real` `--S` `C * cB + S * t` `C * t - S * cB` 1 THEN
  CNSPB_SUBST_LOWER_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < cB - t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   CNSPB_PROD_TAC `C:real` `t - cB` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNSPB_PROD_TAC `C - S` `(&2 * cB - (&3 / &2) * t) - uB` THEN
  CNSPB_PROD_TAC `--(C * t - S * cB)` `&1 / &2 - ((cB + t) * uB + (t - cB) * (vB + aB))` THEN
  SUBGOAL_THEN `(cB - t) * ((C * cB + S * t) * uB + (C * t - S * cB) * (vB + aB)) =
                (C - S) * uB - (C * t - S * cB) * ((cB + t) * uB + (t - cB) * (vB + aB))`
    ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[REAL_NEG_GE0] THEN
  MATCH_MP_TAC CNSPB_NONPOS_OF_MUL THEN EXISTS_TAC `cB - t` THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []);;

let CNSPB_CLOSE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
           REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC];
    RASM_ARITH_TAC];;

(* Lean: impossible *)
let CNSPB_IMPOSSIBLE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB t C S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal C S /\ c977cc_normal cB t /\ c977cc_normal cD sD /\
     sB = --t /\ aD = aB /\ &1 < aD /\
     lcont cD sD uD vD aD /\ linside cD sD uD vD aD (&2) (&457 / &500) /\
     vB + aB <= &2 * cB + &3 * t /\
     &2 * C - (&3 / &2) * S < ABT_lower cB sB uB vB aB C (--S) /\
     vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB (&1) (&0) <= &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                 `&1`; `&0`] CNPB_IMPOSSIBLE) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN
     FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
            REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC];
     REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `uB <= &2 * cB - (&3 / &2) * t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`]
     PBWNA_OF_ENTRY) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
     REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB (&1) (--(&1)) <= &1 / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`]
     CNSPB_DIAGONAL_IMPOSSIBLE) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
     REWRITE_TAC[]]; ALL_TAC] THEN
  CNSPB_CLOSE CNSPB_ENDPOINT_BOUND
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`; `C:real`; `S:real`]);;
