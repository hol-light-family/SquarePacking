(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallTopEndpoint.lean                       *)
(* (N12Compact.FullAuxWallTopEndpoint).  The genuine top endpoint in the     *)
(* signed opposite-square cycle.  D has sD = --S with c977cc_normal cD S;    *)
(* B is either positive (c977cc_normal cB sB) or has sB = --t.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_NegativePoint.ml";;
needs "n12/geometry/FullAuxWallOppositeEscape.ml";;
needs "n12/geometry/FullAuxWallOuterCorner.ml";;

let FAWTE_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let FAWTE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: lower_pp *)
let FAWTE_LOWER_PP = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ &0 <= --x * s + y * c
     ==> ABT_lower c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * v`,
  MATCH_ACCEPT_TAC C981NP_LOWER_PP);;

(* Lean: lower_np *)
let FAWTE_LOWER_NP = prove
 (`forall c s u v a x y. x * c + y * s <= &0 /\ &0 <= --x * s + y * c
     ==> ABT_lower c s u v a x y = (x * c + y * s) * (u + a) + (--x * s + y * c) * v`,
  MATCH_ACCEPT_TAC C981NP_LOWER_NP);;

(* one separating-axis case of `transverse`; D = (cD,sD,uD,vD), B = (cB,sB,uB,vB), *)
(* common side aB                                                               *)
let FAWTE_CASE_TAC nx ny swap radius points =
  let sep = SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aB:real`;
                   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; nx; ny]
                  ABT_SEPARATED in
  let sb ((c,s,u,v),(x,y)) =
    MP_TAC(SPECL [c; s; u; v; `aB:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY sb points THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; RASM_ARITH_TAC];;

(* Lean: transverse *)
let FAWTE_TRANSVERSE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --S /\ c977cc_normal cD S /\ &0 < cB /\ --cB <= sB /\ sB <= cB /\
     aD = aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cD sD uD vD aD (&11 / &10) (&2) /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> vD + aD <= ABT_lower cB sB uB vB aB S cD \/
         ABT_upper cD sD uD vD aD (--sB) cB <= vB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `S = --sD` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aB:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let qD = (`cD:real`,`sD:real`,`uD:real`,`vD:real`)
  and qB = (`cB:real`,`sB:real`,`uB:real`,`vB:real`) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [FAWTE_CASE_TAC `cD:real` `sD:real` false
     (SPECL [`cD:real`; `sD:real`; `aB:real`; `cB:real`; `sB:real`; `aB:real`]
       ABT_PARALLEL_RADIUS)
     [qD,(`&2`,`&2`); qD,(`&11 / &10`,`&2`); qB,(`&33 / &20`,`&47 / &20`)];
   FAWTE_CASE_TAC `--sD:real` `cD:real` false
     (SPECL [`cD:real`; `sD:real`; `aB:real`; `cB:real`; `sB:real`; `aB:real`]
       ABT_TRANSVERSE_RADIUS)
     [qD,(`&33 / &20`,`&33 / &20`); qB,(`&33 / &20`,`&47 / &20`)];
   FAWTE_CASE_TAC `cB:real` `sB:real` true
     (SPECL [`cB:real`; `sB:real`; `aB:real`; `cD:real`; `sD:real`; `aB:real`]
       ABT_PARALLEL_RADIUS)
     [qD,(`&2`,`&2`); qD,(`&11 / &10`,`&2`);
      qB,(`&33 / &20`,`&47 / &20`); qB,(`&1`,`&12 / &5`)];
   FAWTE_CASE_TAC `--sB:real` `cB:real` true
     (SPECL [`cB:real`; `sB:real`; `aB:real`; `cD:real`; `sD:real`; `aB:real`]
       ABT_TRANSVERSE_RADIUS)
     [qD,(`&33 / &20`,`&33 / &20`); qB,(`&33 / &20`,`&47 / &20`)]]);;

(* Lean: defect (private) *)
let FAWTE_DEFECT = prove
 (`forall b t. c977cc_normal b t ==> &1 - b <= (&3 / &5) * t pow 2`,
  MATCH_ACCEPT_TAC C981NP_DEFECT);;

(* Lean: positive_v *)
let FAWTE_POSITIVE_V = prove
 (`forall cD sD uD vD aD cB sB uB vB aB S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --S /\ c977cc_normal cD S /\ c977cc_normal cB sB /\
     &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cD sD uD vD aD (&11 / &10) (&2) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     (vD + aD <= ABT_lower cB sB uB vB aB S cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> &3 * cB - (&8 / &5) * sB < vB + aB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`] FAWTE_DEFECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `&11 / &10`; `&2`;
                `--sB:real`; `cB:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD:real = --S`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  FAWTE_UNFOLD_TAC `linside cD (--S) uD vD aD (&2) (&2)` THEN
  FAWTE_UNFOLD_TAC `linside cB sB uB vB aB (&1) (&113 / &50)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [ALL_TAC; RASM_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 <= S * cB + cD * sB` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FAWTE_PROD `&0 <= (cD - S) * cB` THEN
  FAWTE_PROD `&0 <= S * (cB - sB)` THEN
  SUBGOAL_THEN `&0 <= --S * sB + cD * cB` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `S:real`; `cD:real`]
    FAWTE_LOWER_PP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FAWTE_PROD `&0 <= (S * cB + cD * sB) * ((cB + (&113 / &50) * sB) - uB)` THEN
  FAWTE_PROD `&0 <= (--S * sB + cD * cB) * ((&3 * cB - (&8 / &5) * sB - &1) - vB)` THEN
  FAWTE_PROD `&0 <= cB * sB` THEN
  FAWTE_PROD `&0 <= sB * (cB - sB)` THEN
  FAWTE_PROD `&0 <= sB * sB` THEN
  SUBGOAL_THEN `&1 - cB - (&37 / &50) * sB * sB - (&3 / &5) * cB * sB <= &0 /\
                --(&1) + sB + (&3 / &5) * sB * sB - (&37 / &50) * cB * sB <= &0`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cD * (&1 - cB - (&37 / &50) * sB * sB - (&3 / &5) * cB * sB) <= &0 /\
                S * (--(&1) + sB + (&3 / &5) * sB * sB - (&37 / &50) * cB * sB) <= &0`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC C981NP_MUL_NONPOS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(S * cB + cD * sB) * (cB + (&113 / &50) * sB) +
    (--S * sB + cD * cB) * (&3 * cB - (&8 / &5) * sB - &1) - &2 * (cD + S) =
    cD * (&1 - cB - (&37 / &50) * sB * sB - (&3 / &5) * cB * sB) +
    S * (--(&1) + sB + (&3 / &5) * sB * sB - (&37 / &50) * cB * sB)` MP_TAC THENL
  [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_point *)
let FAWTE_NEGATIVE_POINT = prove
 (`forall cD sD uD vD aD cB sB uB vB aB S t.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --S /\ c977cc_normal cD S /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     (vD + aD <= ABT_lower cB sB uB vB aB S cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> linside cB sB uB vB aB (&8 / &5) (&3)`,
  MATCH_ACCEPT_TAC C981NP_POINT);;
