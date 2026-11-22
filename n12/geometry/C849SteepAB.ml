(* ========================================================================= *)
(* Port of Compact/Geometry/C849SteepAB.lean (N12Compact.C849SteepAB).       *)
(* A complete geometric sector exclusion for the original 849/851 roles.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C849SteepMargins.ml";;
needs "n12/geometry/C849PositiveAbove.ml";;
needs "n12/geometry/FourSquareAAll.ml";;

(* Lean: compose *)
let C849SAB_COMPOSE = prove
 (`forall cA sA cB sB x y. cA * cA + sA * sA = &1
     ==> (cB * sA - sB * cA) * (cA * x + sA * y) +
         (cB * cA + sB * sA) * (--sA * x + cA * y) = --sB * x + cB * y`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING);;

(* Lean: upper_formula *)
let C849SAB_UPPER_FORMULA = prove
 (`forall cA sA uA vA aA cB sB.
     &0 <= cB * cA + sB * sA
     ==> ABT_upper cA sA uA vA aA (--sB) cB =
         (cB * sA - sB * cA) * (uA + aA / &2) +
         (cB * cA + sB * sA) * (vA + aA / &2) +
         aA / &2 * (abs(cB * sA - sB * cA) + (cB * cA + sB * sA))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy;
    REAL_ARITH `-- --sB * sA + cB * cA = cB * cA + sB * sA`] THEN
  REWRITE_TAC[REAL_ARITH `--sB * cA + cB * sA = cB * sA - sB * cA`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN CONV_TAC REAL_RING);;

(* Lean: lower_formula *)
let C849SAB_LOWER_FORMULA = prove
 (`forall cA sA cB sB uB vB aB.
     &0 <= cB * cA + sB * sA
     ==> ABT_lower cB sB uB vB aB (--sA) cA =
         --(cB * sA - sB * cA) * (uB + aB / &2) +
         (cB * cA + sB * sA) * (vB + aB / &2) -
         aB / &2 * (abs(cB * sA - sB * cA) + (cB * cA + sB * sA))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy;
    REAL_ARITH `-- --sA * sB + cA * cB = cB * cA + sB * sA`] THEN
  REWRITE_TAC[REAL_ARITH `abs(--sA * cB + cA * sB) = abs(cB * sA - sB * cA)`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN CONV_TAC REAL_RING);;

let C849SAB_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

let C849SAB_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[] THEN ABT_ARITH_TAC;;

(* Lean: face_modes *)
let C849SAB_FACE_MODES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ &0 <= s /\ &1 < a /\
     lclosed c s u v a (&2) (&113 / &50) /\
     lclosed c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5)
     ==> (c * (&33 / &20) + s * (&47 / &20) <= u /\
          --s * (&47 / &20) + c * (&33 / &20) <= v /\ s <= c) \/
         (c * (&47 / &20) + s * (&33 / &20) <= u /\
          --s * &3 + c * (&12 / &5) <= v /\ &3 / &7 <= s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * (&47 / &20) + s * (&33 / &20) <= u
    ==> c * (&47 / &20) + s * (&33 / &20) <= u /\
        --s * &3 + c * (&12 / &5) <= v /\ &3 / &7 <= s`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&35 * c <= &61 * s` ASSUME_TAC THENL [ABT_ARITH_TAC; ALL_TAC] THEN
    C849SAB_SP_TAC `&13 / &20` `&3 / &4` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C849SAB_MISS_TAC [`c * &3`; `s * &12 / &5`];
      NLIN_FACTS_TAC [] [`&0 <= (&61 * s - &35 * c) * (&61 * s + &35 * c)`] THEN
      NLIN_TAC [SQ_NONNEG `s - &3 / &7`]];
    ALL_TAC] THEN
  ASM_CASES_TAC `c * (&47 / &20) + s * (&33 / &20) <= u` THENL
   [DISJ2_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--s * (&47 / &20) + c * (&33 / &20) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C849SAB_MISS_TAC [`c * &47 / &20`; `s * &33 / &20`]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &10 / &7`]
   [`(&7 / &10) * (c + s) <= &1`] THEN
  SUBGOAL_THEN `c * (&33 / &20) + s * (&47 / &20) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C849SAB_MISS_TAC [`c * &33 / &20`; `s * &47 / &20`]; ALL_TAC] THEN
  ASM_CASES_TAC `s <= c` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ABT_ARITH_TAC]);;

let C849SAB_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC];;

let C849SAB_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC];;

let C849SAB_MARGIN_TAC th =
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN NLIN_TAC ~deg2:false [];
    DISCH_TAC];;

(* Lean: in_frame *)
let C849SAB_IN_FRAME = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cA /\ &0 <= sA /\ &0 < cB /\ &0 <= sB /\ sB <= cB /\
     aA = aB /\ &1 < aB /\
     aB <= sB + cB / &2 /\
     vB + aB <= --sB + &3 * cB /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aB:real`] C849SM_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C849SM_BOUNDS_DEF]) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LINSIDE_CLOSED] THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`]
    C849SAB_FACE_MODES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`; `&1`; `&3`]
    C849SAB_COMPOSE) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `cA:real`; `sA:real`; `&1`; `&3`]
    C849SAB_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C849SAB_LE_MUL_TAC `cB:real` `cA:real` THEN C849SAB_LE_MUL_TAC `sB:real` `sA:real` THEN
  SUBGOAL_THEN `&0 <= cB * cA + sB * sA` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`; `cB:real`; `sB:real`]
    C849SAB_UPPER_FORMULA) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849SAB_LOWER_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cB * sA - sB * cA <= &0 ==> sA <= cA` ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C849SAB_LE_MUL_TAC `cA:real` `cB - sB` THEN C849SAB_LT_MUL_TAC `cB:real` `sA - cA` THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  C849SAB_LT_MUL_TAC `aB - &1` `&1 + (cB * cA + sB * sA)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside]) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
    is_disj(concl th) && is_conj(lhand(concl th)))) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `vB:real`)) (lhand(concl th)))) THEN
  ASM_CASES_TAC `&0 <= cB * sA - sB * cA` THEN
  (SUBGOAL_THEN `abs(cB * sA - sB * cA) = if &0 <= cB * sA - sB * cA
                   then cB * sA - sB * cA else --(cB * sA - sB * cA)` MP_TAC THENL
    [REAL_ARITH_TAC;
     ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) THENL
   [(* mode 1, axis B, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uA - (cA * &33 / &20 + sA * &47 / &20)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &47 / &20 + cA * &33 / &20)` THEN
    C849SAB_LT_MUL_TAC `aB - &1` `&1 + (cB * cA + sB * sA) + (cB * sA - sB * cA)` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERV_B_POS THEN NLIN_TAC ~deg2:false [];
    (* mode 1, axis B, e < 0 *)
    C849SAB_LE_MUL_TAC `--(cB * sA - sB * cA)` `cA * &2 + sA * &113 / &50 - uA` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &47 / &20 + cA * &33 / &20)` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERV_B_NEG THEN NLIN_TAC ~deg2:false [];
    (* mode 1, axis A, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uB + aB - (&2 * cB + &3 * sB)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `--sB + &3 * cB - aB - vB` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERV_A_POS THEN NLIN_TAC ~deg2:false [];
    (* mode 1, axis A, e < 0 *)
    C849SAB_LE_MUL_TAC `--(cB * sA - sB * cA)` `cB * &33 / &20 + sB * &47 / &20 - uB` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `--sB + &3 * cB - aB - vB` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERV_A_NEG THEN NLIN_TAC ~deg2:false [];
    (* mode 2, axis B, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uA - (cA * &47 / &20 + sA * &33 / &20)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &3 + cA * &12 / &5)` THEN
    C849SAB_LT_MUL_TAC `aB - &1` `&1 + (cB * cA + sB * sA) + (cB * sA - sB * cA)` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERU_B_POS THEN NLIN_TAC ~deg2:false [];
    (* mode 2, axis B, e < 0 *)
    SUBGOAL_THEN `sA <= cA` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    C849SAB_LE_MUL_TAC `--(cB * sA - sB * cA)` `cA * &2 + sA * &113 / &50 - uA` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &3 + cA * &12 / &5)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `(&3 / &4) * cA - (&13 / &20) * sA` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERV_B_NEG THEN NLIN_TAC ~deg2:false [];
    (* mode 2, axis A, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uB + aB - (&2 * cB + &3 * sB)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `--sB + &3 * cB - aB - vB` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERU_A_POS THEN NLIN_TAC ~deg2:false [];
    (* mode 2, axis A, e < 0 *)
    SUBGOAL_THEN `sA <= cA` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    C849SAB_LE_MUL_TAC `--(cB * sA - sB * cA)` `cB * &33 / &20 + sB * &47 / &20 - uB` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `--sB + &3 * cB - aB - vB` THEN
    C849SAB_MARGIN_TAC C849SM_LOWERV_A_NEG THEN NLIN_TAC ~deg2:false []]);;

(* Lean: impossible *)
let C849SAB_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     aA = aB /\ &1 < aB /\ &1 < aR /\
     lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&81 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     vB + aB <= --sB + &3 * cB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] FSAA_POINT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LINSIDE_CLOSED] THEN ABT_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849PA_B_LOWER_FACE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    DISCH_TAC THEN UNDISCH_TAC `ldisj cA sA uA vA aB cB sB uB vB aB` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&5 / &2`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&3`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM ldisj] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `aB <= sB + cB / &2` ASSUME_TAC THENL [ABT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849SAB_IN_FRAME) THEN
  ASM_REWRITE_TAC[ldisj] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[]);;
