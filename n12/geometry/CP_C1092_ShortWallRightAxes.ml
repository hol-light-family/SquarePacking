(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallRightAxes.lean                  *)
(* (N12Compact.C1092ShortWallRightAxes).  A signed canonical right-wall      *)
(* frame leaves only its two forward longitudinal separators.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallNarrow.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

let C1092SWRA_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWRA_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWRA_LIN_TAC; DISCH_TAC];;

let C1092SWRA_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWRA_LIN_TAC; DISCH_TAC];;

(* Lean: transverse (private) *)
let C1092SWRA_TRANSVERSE = prove
 (`forall cA sA uA vA aA cR (sR:real).
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\
     c977cc_normal cA sA /\ C1092SWN_narrowData cA sA uA vA aA /\
     &0 < cR /\ abs sR <= cR /\ &1 < aA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20)
     ==> ABT_lower cA sA uA vA aA (--sR) cR < --sR * &3 + cR * (&1197 / &500) /\
         --sR * (&1543 / &500) + cR * &2 < ABT_upper cA sA uA vA aA (--sR) cR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092SWN_narrowData] o
    check (fun th -> can (term_match [] `C1092SWN_narrowData c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_NARROW_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWRA_LIN_TAC; STRIP_TAC] THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  SUBGOAL_THEN `&0 < cA` ASSUME_TAC THENL [C1092SWRA_LIN_TAC; ALL_TAC] THEN
  let sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  ABT_SB_TAC sqA `&113 / &50` `&2` `--sR` `cR:real` THEN
  ABT_SB_TAC sqA `&47 / &20` `&47 / &20` `--sR` `cR:real` THEN
  MP_TAC(SPECL (sqA @ [`--sR`; `cR:real`]) C1092WS_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  C1092SWRA_LE_MUL_TAC `sA:real` `&1 - cA` THEN
  C1092SWRA_LE_MUL_TAC `cA:real` `sA:real` THEN
  SUBGOAL_THEN `&0 <= sA pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sR` THENL
   [CONJ_TAC THENL [ALL_TAC; C1092SWRA_LIN_TAC] THEN
    ASM_CASES_TAC `cA * sR <= sA * cR` THENL
     [C1092SWRA_LE_MUL_TAC `cR:real` `cA - &4 * sA` THEN
      SUBGOAL_THEN `&4 * sR <= cR` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        C1092SWRA_LT_MUL_TAC `cA:real` `&4 * sR - cR` THEN C1092SWRA_LIN_TAC;
        ALL_TAC] THEN
      C1092SWRA_LIN_TAC;
      ALL_TAC] THEN
    C1092SWRA_LT_MUL_TAC `cA:real` `cR:real` THEN
    C1092SWRA_LE_MUL_TAC `sA:real` `sR:real` THEN
    SUBGOAL_THEN `min (--sR * cA + cR * sA) (&0) = --sR * cA + cR * sA /\
                  min (-- --sR * sA + cR * cA) (&0) = &0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[real_min] THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    C1092SWRA_LE_MUL_TAC `cA * sR - sA * cR` `uA - &2 * (cA + sA)` THEN
    C1092SWRA_LE_MUL_TAC `cA * cR + sA * sR` `&3 * cA - (&1197 / &500) * sA - (vA + aA)` THEN
    C1092SWRA_LT_MUL_TAC `aA - &1` `(cA * cR + sA * sR) + (cA * sR - sA * cR)` THEN
    C1092SWRA_LE_MUL_TAC `cR - sR`
      `cA - sA - &303 / &500 + sA pow 2 + (&197 / &500) * cA * sA` THEN
    C1092SWRA_LE_MUL_TAC `sR:real`
      `(cA - sA - &303 / &500 + sA pow 2 + (&197 / &500) * cA * sA) +
       (cA + sA - &1 + (&197 / &500) * sA pow 2 - cA * sA)` THEN
    SUBGOAL_THEN
     `(--sR * &3 + cR * (&1197 / &500)) -
      (--(cA * sR - sA * cR) * (&2 * (cA + sA) + &1) +
       (cA * cR + sA * sR) * (&3 * cA - (&1197 / &500) * sA - &1)) =
      cR * (cA - sA - &303 / &500 + sA pow 2 + (&197 / &500) * cA * sA) +
      sR * (cA + sA - &1 + (&197 / &500) * sA pow 2 - cA * sA)` ASSUME_TAC THENL
     [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092SWRA_LIN_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [C1092SWRA_LIN_TAC; ALL_TAC] THEN
  C1092SWRA_LT_MUL_TAC `cR:real` `cA - sA` THEN
  C1092SWRA_LE_MUL_TAC `sA:real` `cR - --sR` THEN
  C1092SWRA_LE_MUL_TAC `cA:real` `--sR` THEN
  C1092SWRA_LE_MUL_TAC `sA:real` `cR:real` THEN
  SUBGOAL_THEN `max (--sR * cA + cR * sA) (&0) = --sR * cA + cR * sA /\
                max (-- --sR * sA + cR * cA) (&0) = -- --sR * sA + cR * cA`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[real_max] THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092SWRA_LE_MUL_TAC `cA * --sR + sA * cR` `uA - &2 * (cA + sA)` THEN
  C1092SWRA_LT_MUL_TAC `cA * cR - sA * --sR` `vA + aA - (--sA * &5 / &2 + cA * &3)` THEN
  C1092SWRA_LE_MUL_TAC `cA * --sR + sA * cR` `aA - &1` THEN
  C1092SWRA_LE_MUL_TAC `sA:real` `&1 / &4 - sA` THEN
  C1092SWRA_LE_MUL_TAC `cR - --sR` `&1 - sA pow 2 - cA * sA / &2 + sA` THEN
  C1092SWRA_LE_MUL_TAC `--sR`
    `(&1 - sA pow 2 - cA * sA / &2 + sA) + (cA - &543 / &500 + sA pow 2 / &2 - cA * sA)` THEN
  SUBGOAL_THEN
   `(cA * --sR + sA * cR) * (&2 * (cA + sA) + &1) +
    (cA * cR - sA * --sR) * (&3 * cA - (&5 / &2) * sA) -
    (--sR * (&1543 / &500) + cR * &2) =
    cR * (&1 - sA pow 2 - cA * sA / &2 + sA) +
    --sR * (cA - &543 / &500 + sA pow 2 / &2 - cA * sA)` ASSUME_TAC THENL
   [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092SWRA_LIN_TAC);;

(* Lean: alternatives *)
let C1092SWRA_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\
     c977cc_normal cA sA /\ C1092SWN_narrowData cA sA uA vA aA /\
     &0 < cR /\ abs sR <= cR /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cR:real`; `sR:real`]
    C1092SWRA_TRANSVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092SWN_narrowData] o
    check (fun th -> can (term_match [] `C1092SWN_narrowData c s u v a`) (concl th))) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  ABT_PAIR_TAC "A" "R"
    ["A",(`&113 / &50`,`&2`); "R",(`&1543 / &500`,`&2`); "R",(`&3`,`&1197 / &500`)]);;
