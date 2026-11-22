(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomWallNeighborAxis.lean (Jatloe,     *)
(* N12-jatloe; namespace N12Compact.PositiveBottomWallNeighborAxis).         *)
(* The positive bottom wall's own transverse separator is incompatible with  *)
(* a central-neighbor-owned incoming axis.  Lean upper/lower are ABT_upper/  *)
(* ABT_lower; positive_frame_wall_bounds is used through TSS_BOTTOM_WALL.    *)
(* The OpenSquare invariants of A are explicit hypotheses.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveBottomWallCentralAxis.ml";;

let PBWNA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PBWNA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PBWNA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PBWNA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: margin (private) *)
let PBWNA_MARGIN = prove
 (`forall c t d r. c977cc_normal c t /\ c977cc_normal d r
     ==> d * ((--r * c - d * t) * (&2 * c - (&3 / &2) * t + &1) +
              (d * c - r * t) * (&2 * c + &3 * t - &1)) -
         d + &2 * d * r + (&457 / &500) * r pow 2 <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBWNA_NORMAL_TAC THEN
  PBWNA_PROD_TAC `&1 - c` `c + &2 * t - &1` THEN
  SUBGOAL_THEN `&2 - t pow 2 / &2 + c * t - c - t <= &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWNA_PROD_TAC `&1 - c` `(&3 / &5) * c - &2 / &5` THEN
  NLIN_FACTS_TAC [] [`&1 - c <= (&3 / &5) * t pow 2`] THEN
  PBWNA_PROD_TAC `t:real` `c - &7 / &10` THEN
  SUBGOAL_THEN `&53 / &100 <= t pow 2 + c * t / &2 + c - t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  PBWNA_PROD_TAC `&1 - d` `(&3 / &5) * d - &2 / &5` THEN
  NLIN_FACTS_TAC [] [`(&2 / &5) * r pow 2 <= d * (&1 - d)`] THEN
  PBWNA_PROD_TAC `d:real` `r:real` THEN
  PBWNA_PROD_TAC `d pow 2` `&1 - (&2 - t pow 2 / &2 + c * t - c - t)` THEN
  PBWNA_PROD_TAC `d * r` `(t pow 2 + c * t / &2 + c - t) - &53 / &100` THEN
  PBWNA_PROD_TAC `r:real` `d - r` THEN
  SUBGOAL_THEN
   `d * ((--r * c - d * t) * (&2 * c - (&3 / &2) * t + &1) +
         (d * c - r * t) * (&2 * c + &3 * t - &1)) -
    d + &2 * d * r + (&457 / &500) * r pow 2 =
    d pow 2 * (&2 - t pow 2 / &2 + c * t - c - t) - d -
    d * r * (t pow 2 + c * t / &2 + c - t) + (&457 / &500) * r pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: of_entry *)
let PBWNA_OF_ENTRY = prove
 (`forall cD sD uD vD aD cB sB uB vB aB t.
     c977cc_normal cD sD /\ c977cc_normal cB t /\ sB = --t /\ aD = aB /\ &1 < aD /\
     lcont cD sD uD vD aD /\ linside cD sD uD vD aD (&2) (&457 / &500) /\
     vB + aB <= &2 * cB + &3 * t /\ &2 * cB - (&3 / &2) * t <= uB /\
     vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  PBWNA_USE PBWNA_MARGIN [`cB:real`; `t:real`; `cD:real`; `sD:real`] THEN
  PBWNA_NORMAL_TAC THEN
  SUBGOAL_THEN `cD * cD + sD * sD = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sD = sD` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PBWNA_PROD_TAC `sD:real` `cB:real` THEN PBWNA_PROD_TAC `cD:real` `t:real` THEN
  PBWNA_PROD_TAC `cD:real` `cB - t` THEN PBWNA_PROD_TAC `t:real` `cD - sD` THEN
  SUBGOAL_THEN `(--sD * cB - cD * t) <= &0 /\ &0 <= (--sD * t + cD * cB)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWNA_USE C977NCO_LOWER_NEGATIVE_NONPOS
    [`cB:real`; `--t`; `uB:real`; `vB:real`; `aD:real`; `t:real`; `--sD`; `cD:real`] THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
  PBWNA_PROD_TAC `--((--sD * cB - cD * t))` `uB - (&2 * cB - (&3 / &2) * t)` THEN
  PBWNA_PROD_TAC `(--sD * t + cD * cB)` `(&2 * cB + &3 * t) - (vB + aD)` THEN
  PBWNA_PROD_TAC `cD:real` `--((--sD * cB - cD * t)) * (uB - (&2 * cB - (&3 / &2) * t))` THEN
  PBWNA_PROD_TAC `cD:real` `(--sD * t + cD * cB) * ((&2 * cB + &3 * t) - (vB + aD))` THEN
  MP_TAC(ASSUME `linside cD sD uD vD aD (&2) (&457 / &500)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PBWNA_PROD_TAC `sD:real` `&2 * cD + (&457 / &500) * sD - uD` THEN
  PBWNA_PRODLT_TAC `cD:real` `&1 + (--sD * t + cD * cB) - (--sD * cB - cD * t)` THEN
  PBWNA_PRODLT_TAC `aD - &1` `cD * (&1 + (--sD * t + cD * cB) - (--sD * cB - cD * t))` THEN
  PBWNA_PROD_TAC `cD:real`
    `((--sD * cB - cD * t) * (uB + aD) + (--sD * t + cD * cB) * vB) - (vD + aD)` THEN
  SUBGOAL_THEN
   `cD * (((--sD * cB - cD * t) * (uB + aD) + (--sD * t + cD * cB) * vB) - (vD + aD)) =
    (cD * ((--sD * cB - cD * t) * (&2 * cB - (&3 / &2) * t + &1) + (--sD * t + cD * cB) * (&2 * cB + &3 * t - &1)) - cD + &2 * cD * sD + (&457 / &500) * sD pow 2) - cD * (--((--sD * cB - cD * t)) * (uB - (&2 * cB - (&3 / &2) * t))) -
    cD * ((--sD * t + cD * cB) * (&2 * cB + &3 * t - (vB + aD))) - (sD * uD + cD * vD) -
    sD * (&2 * cD + (&457 / &500) * sD - uD) - (aD - &1) * cD * (&1 + (--sD * t + cD * cB) - (--sD * cB - cD * t))`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible *)
let PBWNA_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD cB sB uB vB aB t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cD sD /\ c977cc_normal cB t /\ sB = --t /\ aD = aB /\ &1 < aD /\
     lcont cD sD uD vD aD /\ linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     vB + aB <= &2 * cB + &3 * t /\
     ABT_upper cA sA uA vA aA cB sB <= uB /\
     vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBWNA_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    `&2` `&3 / &2` `cB:real` `--t` THEN
  MATCH_MP_TAC PBWNA_OF_ENTRY THEN
  MAP_EVERY EXISTS_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                        `cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;
