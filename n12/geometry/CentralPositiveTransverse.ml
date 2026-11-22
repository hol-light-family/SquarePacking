(* ========================================================================= *)
(* Port of Compact/Geometry/CentralPositiveTransverse.lean (Jatloe).          *)
(* A positive centre owner cannot receive the southeast neighbour on that    *)
(* neighbour's transverse axis.  Normal: c977cc_normal; lower: ABT_lower;    *)
(* CentralCenterPairIncoming.right_alternatives: CCPI_RIGHT_ALTERNATIVES.    *)
(* (Not to be confused with PositiveCentralTransverse.ml, tag PCT_.)         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralCenterPairIncoming.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

let CPTR_NORMAL_TAC = PCT_NORMAL_TAC;;

(* support value when the U coefficient is <= 0 and the V coefficient >= 0 *)
let CPTR_LOWER_NP = prove
 (`forall c s u v a nx ny. nx * c + ny * s <= &0 /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: margin *)
let CPTR_MARGIN = prove
 (`forall C S c s. c977cc_normal C S /\ c977cc_normal c s
     ==> &0 < &1 + (C * c + S * s) -
              (c * (&27 / &20 - (&7 / &20) * S pow 2 + (&7 / &20) * C * S) +
               s * (&1 + (&7 / &20) * S pow 2 + (&7 / &20) * C * S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CPTR_NORMAL_TAC THEN
  ABBREV_TAC `x = &27 / &20 - C - (&7 / &20) * S pow 2 + (&7 / &20) * C * S` THEN
  ABBREV_TAC `y = &1 - S + (&7 / &20) * S pow 2 + (&7 / &20) * C * S` THEN
  PCT_PROD_TAC `C:real` `C + S:real` THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL
  [EXPAND_TAC "x" THEN NLIN_TAC []; ALL_TAC] THEN
  PCT_PROD_TAC `C - S:real` `&1 - (&7 / &20) * (C + S)` THEN
  SUBGOAL_THEN `y - x = (C - S) * (&1 - (&7 / &20) * (C + S))` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
   UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `x <= y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `C + S - &1:real` `&1 - (&7 / &20) * (C + S + &1)` THEN
  SUBGOAL_THEN `&1 + (&7 / &10) * C * S <= C + S` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `x + y <= &27 / &20` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `c - s:real` `y - x:real` THEN
  PCT_PROD_TAC `&10 / &7 - (c + s)` `x + y:real` THEN
  SUBGOAL_THEN `c * x + s * y <= &27 / &28` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 + (C * c + S * s) -
    (c * (&27 / &20 - (&7 / &20) * S pow 2 + (&7 / &20) * C * S) +
     s * (&1 + (&7 / &20) * S pow 2 + (&7 / &20) * C * S)) = &1 - c * x - s * y`
  SUBST1_TAC THENL
  [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: impossible *)
let CPTR_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cA sA /\ c977cc_normal cB sB /\ aA = aB /\ &1 < aA /\
     linside cA sA uA vA aA (&2) (&2) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     ~linside cB sB uB vB aB (&3) (&1) /\
     vB + aB <= ABT_lower cA sA uA vA aA (--sB) cB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] CPTR_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CPTR_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aB`)) THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&2) (&2)` THEN
  UNDISCH_TAC `linside cB sB uB vB aA (&47 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `linside cB sB uB vB aA (&3) (&87 / &50)` THEN
  UNDISCH_TAC `~linside cB sB uB vB aA (&3) (&1)` THEN
  REWRITE_TAC[linside] THEN DISCH_TAC THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cB - &3 * sB <= vB` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `cA:real` `cB:real` THEN PCT_PROD_TAC `sA:real` `sB:real` THEN
  SUBGOAL_THEN `&0 < cA * cB + sA * sB` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cA sA uA vA aA (--sB) cB <=
                &2 * (sA * cB - cA * sB) * (cA + sA) + (cA * cB + sA * sB) * vA`
  ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= sA * cB - cA * sB` THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `--sB`; `cB:real`] PCT_LOWER_PP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    PCT_PROD_TAC `sA * cB - cA * sB` `&2 * (cA + sA) - uA` THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `--sB`; `cB:real`] CPTR_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    PCT_PROD_TAC `--(sA * cB - cA * sB)` `(uA + aA) - &2 * (cA + sA)` THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  PCT_PROD_TAC `cA * cB + sA * sB` `((&47 / &20) * cA - (&33 / &20) * sA) - (vA + aA)` THEN
  PCT_PRODLT_TAC `&1 + (cA * cB + sA * sB)` `aA - &1` THEN
  SUBGOAL_THEN
   `&2 * (sA * cB - cA * sB) * (cA + sA) +
    (cA * cB + sA * sB) * ((&47 / &20) * cA - (&33 / &20) * sA) - cB + &3 * sB =
    cB * (&27 / &20 - (&7 / &20) * sA pow 2 + (&7 / &20) * cA * sA) +
    sB * (&1 + (&7 / &20) * sA pow 2 + (&7 / &20) * cA * sA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: right_alternatives *)
let CPTR_RIGHT_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cA sA /\ &0 < cB /\ abs sB <= cB /\ aA = aB /\ &1 < aA /\
     linside cA sA uA vA aA (&2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     ~linside cB sB uB vB aB (&3) (&1) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> uA + aA <= ABT_lower cB sB uB vB aB cA sA \/
         ABT_upper cA sA uA vA aA cB sB <= uB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cA sA`)) THEN
  MP_TAC(ASSUME `c977cc_normal cA sA`) THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    CCPI_RIGHT_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  MATCH_MP_TAC CPTR_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC);;
