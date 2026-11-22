(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomOwnTransverse.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.NegativeBottomOwnTransverse).            *)
(* The steep negative singleton cannot precede a negative bottom wall below  *)
(* the negative central neighbour.  Lean lower is ABT_lower; boundary is     *)
(* c977cc_boundary.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveBottomNegativeWallMixed.ml";;

let NBOT_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let NBOT_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let NBOT_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: neighbor_support (private) *)
let NBOT_NEIGHBOR_SUPPORT = prove
 (`forall cB sB uB vB aB t d r.
     sB = --t /\ c977cc_normal cB t /\ c977cc_normal d r /\ &1 <= aB /\ t <= &3 / &10 /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t
     ==> ABT_lower cB sB uB vB aB r d <= (&47 / &20) * r + (&13 / &10) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  NBOT_USE PBNWM_WIDE [`cB:real`; `t:real`] THEN NBOT_NORMAL_TAC THEN
  NBOT_PROD_TAC `r:real` `t:real` THEN NBOT_PROD_TAC `d:real` `cB:real` THEN
  NBOT_PROD_TAC `t:real` `&1 - cB` THEN NBOT_PROD_TAC `cB:real` `&1 - cB` THEN
  ASM_CASES_TAC `&0 <= (r * cB - d * t)` THENL
  [NBOT_USE C977NCO_LOWER_NEGATIVE_POS
     [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`; `r:real`; `d:real`] THEN
   NBOT_PROD_TAC `(r * cB - d * t)` `(&3 * cB - t) - (uB + aB)` THEN
   NBOT_PROD_TAC `(r * t + d * cB)` `(&2 * cB + &3 * t) - (vB + aB)` THEN
   NBOT_PROD_TAC `(r * cB - d * t) + (r * t + d * cB)` `aB - &1` THEN
   SUBGOAL_THEN `(r * cB - d * t) * (&3 * cB - t - &1) + (r * t + d * cB) * (&2 * cB + &3 * t - &1) = r * (&3 + cB * t - cB - t) + d * (&2 - t pow 2 + t - cB)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_FACTS_TAC [] [`(&3 + cB * t - cB - t) <= &47 / &20`; `(&2 - t pow 2 + t - cB) <= &13 / &10`] THEN
   NBOT_PROD_TAC `r:real` `&47 / &20 - (&3 + cB * t - cB - t)` THEN
   NBOT_PROD_TAC `d:real` `&13 / &10 - (&2 - t pow 2 + t - cB)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  NBOT_USE C977NCO_LOWER_NEGATIVE_NONPOS
    [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`; `r:real`; `d:real`] THEN
  MP_TAC(ASSUME `linside cB (--t) uB vB aB (&47 / &20) (&33 / &20)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  NBOT_PROD_TAC `--((r * cB - d * t))` `(uB + aB) - ((&47 / &20) * cB - (&33 / &20) * t)` THEN
  NBOT_PROD_TAC `(r * t + d * cB)` `(&2 * cB + &3 * t) - (vB + aB)` THEN
  NBOT_PROD_TAC `(r * t + d * cB)` `aB - &1` THEN
  SUBGOAL_THEN
   `(r * cB - d * t) * ((&47 / &20) * cB - (&33 / &20) * t) + (r * t + d * cB) * (&2 * cB + &3 * t - &1) =
    r * (&47 / &20 + (&13 / &20) * t pow 2 + (&7 / &20) * cB * t - t) + d * (&2 - (&7 / &20) * t pow 2 + (&13 / &20) * cB * t - cB)` ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NBOT_PROD_TAC `t:real` `&1 - (&13 / &20) * t - (&7 / &20) * cB` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
    [`cB * t <= &3 / &10`; `(&47 / &20 + (&13 / &20) * t pow 2 + (&7 / &20) * cB * t - t) <= &47 / &20`; `(&2 - (&7 / &20) * t pow 2 + (&13 / &20) * cB * t - cB) <= &13 / &10`] THEN
  NBOT_PROD_TAC `r:real` `&47 / &20 - (&47 / &20 + (&13 / &20) * t pow 2 + (&7 / &20) * cB * t - t)` THEN
  NBOT_PROD_TAC `d:real` `&13 / &10 - (&2 - (&7 / &20) * t pow 2 + (&13 / &20) * cB * t - cB)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: support_bound *)
let NBOT_SUPPORT_BOUND = prove
 (`forall cD sD uD vD aD cB sB uB vB aB r t p s.
     sD = --r /\ sB = --t /\
     c977cc_normal p s /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aD = aB /\ &1 <= aD /\ t <= &3 / &10 /\ &47 / &100 <= s /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     vD + aD <= ABT_lower cB sB uB vB aB r cD
     ==> ABT_lower cD sD uD vD aD s p <= &2 * s + (&3 / &5) * p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NBOT_USE NBOT_NEIGHBOR_SUPPORT
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`; `cD:real`; `r:real`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  NBOT_NORMAL_TAC THEN
  NBOT_PROD_TAC `s:real` `r:real` THEN NBOT_PROD_TAC `p:real` `cD:real` THEN
  MP_TAC(ASSUME `linside cD (--r) uD vD aD (&2) (&457 / &500)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ABT_lower cD (--r) uD vD aD s p <= (s * cD - p * r) * (&2 * cD - (&457 / &500) * r) + (s * r + p * cD) * vD`
  ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= (s * cD - p * r)` THENL
   [NBOT_USE C977NCO_LOWER_NEGATIVE_POS
      [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`; `r:real`; `s:real`; `p:real`] THEN
    NBOT_PROD_TAC `(s * cD - p * r)` `(&2 * cD - (&457 / &500) * r) - uD` THEN RASM_ARITH_TAC;
    NBOT_USE C977NCO_LOWER_NEGATIVE_NONPOS
      [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`; `r:real`; `s:real`; `p:real`] THEN
    NBOT_PROD_TAC `--((s * cD - p * r))` `(uD + aD) - (&2 * cD - (&457 / &500) * r)` THEN RASM_ARITH_TAC];
   ALL_TAC] THEN
  NBOT_PROD_TAC `(s * r + p * cD)` `(&47 / &20) * r + (&13 / &10) * cD - &1 - vD` THEN
  SUBGOAL_THEN
   `(s * cD - p * r) * (&2 * cD - (&457 / &500) * r) + (s * r + p * cD) * ((&47 / &20) * r + (&13 / &10) * cD - &1) =
    &2 * s + (&457 / &500) * p - (s * r + p * cD) + (s * r + p * cD) * ((&7 / &20) * r + (&193 / &500) * cD)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&7 / &20 - (&11 / &20) * r`;
                  SQ_NONNEG `&193 / &500 - (&11 / &20) * cD`]
    [`(&7 / &20) * r + (&193 / &500) * cD <= &11 / &20`] THEN
  NBOT_PROD_TAC `(s * r + p * cD)` `&11 / &20 - ((&7 / &20) * r + (&193 / &500) * cD)` THEN
  NBOT_PROD_TAC `r:real` `&5 / &7 - r` THEN
  NBOT_PROD_TAC `&1 - cD` `cD - &7 / &10` THEN
  NLIN_FACTS_TAC [] [`&1 - cD <= (&3 / &7) * r`] THEN
  NBOT_PROD_TAC `&1 - p` `&1 - cD` THEN
  NBOT_PROD_TAC `r:real` `s - &47 / &100` THEN
  SUBGOAL_THEN `p <= (s * r + p * cD)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible *)
let NBOT_IMPOSSIBLE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB r t p s.
     sD = --r /\ sB = --t /\
     c977cc_normal p s /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aD = aB /\ &1 <= aD /\ t <= &3 / &10 /\ &47 / &100 <= s /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     c977cc_boundary p s < ABT_lower cD sD uD vD aD s p /\
     vD + aD <= ABT_lower cB sB uB vB aB r cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NBOT_USE NBOT_SUPPORT_BOUND
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `t:real`;
     `p:real`; `s:real`] THEN
  NBOT_USE C977CSB_BOUNDARY_HORIZONTAL [`p:real`; `s:real`] THEN
  NBOT_NORMAL_TAC THEN RASM_ARITH_TAC);;
