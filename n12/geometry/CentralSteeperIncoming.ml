(* ========================================================================= *)
(* Port of Compact/Geometry/CentralSteeperIncoming.lean (Jatloe, N12-jatloe; *)
(* namespace N12Compact.CentralSteeperIncoming).  The reversed positive      *)
(* incoming-axis order retains the actual lower corner escape and inward     *)
(* upper-U cap.  Normal is c977cc_normal; lower is ABT_lower, lower_in_bands *)
(* C977NCO_LOWER_IN_BANDS; the private excess is csti_excess.  K, H are      *)
(* written out.  The OpenSquare invariants are explicit hypotheses.          *)
(* Tag CSTI_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let CSTI_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CSTI_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: excess (private) *)
let csti_excess = new_definition
 `csti_excess (C:real) S c s = C * (&1 - c) * (&1 - s) + S * (c * (&1 - c) - s)`;;

(* Lean: excess_bound (private) *)
let CSTI_EXCESS_BOUND = prove
 (`forall C S c s. c977cc_normal C S /\ c977cc_normal c s
     ==> csti_excess C S c s <= (&9 / &100) * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CSTI_NORMAL_TAC THEN
  SUBGOAL_THEN `c * (&1 - c) - s <= &0` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `&1 - c`]; ALL_TAC] THEN
  SUBGOAL_THEN `(c + s) pow 2 <= &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &71 / &50` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  CSTI_PROD_TAC `&71 / &50 - (c + s)` `c + s + &71 / &50 - &2` THEN
  SUBGOAL_THEN `(&1 - c) * (&1 - s) <= &9 / &100` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CSTI_PROD_TAC `C:real` `&9 / &100 - (&1 - c) * (&1 - s)` THEN
  CSTI_PROD_TAC `S:real` `--(c * (&1 - c) - s)` THEN
  REWRITE_TAC[csti_excess] THEN NLIN_TAC ~deg2:false []);;

(* Lean: excess_small (private) *)
let CSTI_EXCESS_SMALL = prove
 (`forall C S c s. c977cc_normal C S /\ c977cc_normal c s /\ &0 < csti_excess C S c s
     ==> S < &2 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CSTI_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c = &1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   UNDISCH_TAC `&0 < csti_excess C S (&1) (&0)` THEN
   REWRITE_TAC[csti_excess] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 * C <= &7 * S` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   CSTI_PROD_TAC `&3 * C - &7 * S` `&3 * C + &7 * S` THEN
   CSTI_PROD_TAC `S - &2 / &5` `S + &2 / &5` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&7 * s <= &3 * (&1 + c)` ASSUME_TAC THENL
  [SUBGOAL_THEN `s <= &5 / &7` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CSTI_PROD_TAC `C:real` `&3 * (&1 + c) - &7 * s` THEN
  CSTI_PROD_TAC `&1 + c` `&7 * S - &3 * C` THEN
  SUBGOAL_THEN `C * s <= S * (&1 + c)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CSTI_PROD_TAC `&1 - c` `&1 - s` THEN
  CSTI_PROD_TAC `(&1 - c) * (&1 - s)` `S * (&1 + c) - C * s` THEN
  CSTI_PROD_TAC `S:real` `s:real` THEN
  CSTI_PROD_TAC `S * s` `&1 - c` THEN
  SUBGOAL_THEN `s * csti_excess C S c s =
                (&1 - c) * (&1 - s) * (C * s - S * (&1 + c)) - S * s * (&1 - c)` ASSUME_TAC THENL
  [REWRITE_TAC[csti_excess] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  MP_TAC(SPECL [`s:real`; `csti_excess C S c s`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_cap *)
let CSTI_CENTRAL_CAP = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cA sA /\ c977cc_normal cB sB /\ &1 <= aB /\
     linside cA sA uA vA aA (&2) (&2) /\
     sA * cB < cA * sB /\ cB - &3 * sB <= vB /\ uB + aB <= &3 * cB + &2 * sB /\
     uA + aA <= ABT_lower cB sB uB vB aB cA sA
     ==> sA < &2 / &5 /\ uA + aA <= &2 * (cA + sA) + (&9 / &100) * cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] CSTI_EXCESS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CSTI_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cA * cB + sA * sB` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sA * cB - cA * sB <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB cA sA =
                (cA * cB + sA * sB) * uB + (sA * cB - cA * sB) * (vB + aB)` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   REWRITE_TAC[REAL_ARITH `--cA * sB + sA * cB = sA * cB - cA * sB`] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  CSTI_PROD_TAC `cA * cB + sA * sB` `(&3 * cB + &2 * sB) - (uB + aB)` THEN
  CSTI_PROD_TAC `--(sA * cB - cA * sB)` `vB - (cB - &3 * sB)` THEN
  CSTI_PROD_TAC `(cA * cB + sA * sB) - (sA * cB - cA * sB)` `aB - &1` THEN
  SUBGOAL_THEN
   `(cA * cB + sA * sB) * (&3 * cB + &2 * sB - &1) + (sA * cB - cA * sB) * (cB - &3 * sB + &1) =
    &2 * (cA + sA) + csti_excess cA sA cB sB` ASSUME_TAC THENL
  [REWRITE_TAC[csti_excess] THEN UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB cA sA <= &2 * (cA + sA) + csti_excess cA sA cB sB`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < csti_excess cA sA cB sB` ASSUME_TAC THENL
  [STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME `linside cA sA uA vA aA (&2) (&2)`)) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CSTI_EXCESS_SMALL THEN
   MAP_EVERY EXISTS_TAC [`cA:real`; `cB:real`; `sB:real`] THEN ASM_REWRITE_TAC[];
   ASM_REAL_ARITH_TAC]);;
