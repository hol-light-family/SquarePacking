(* ========================================================================= *)
(* Port of Compact/Geometry/C696PositiveCorner.lean (Jatloe, N12-jatloe)     *)
(* (namespace N12Compact.C696PositiveCorner).                                *)
(* Signed corner sector: positive bottom singleton O, negative central A.    *)
(* Lean upper/lower are ABT_upper/ABT_lower; a square with A.s = -T is       *)
(* cA sA uA vA aA with the hypothesis sA = --T; the SAT step is              *)
(* ABT_FOUR_AXES.                                                            *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C696CornerMargins.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let C696PC_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C696PC_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let C696PC_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let C696PC_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let C696PC_UPPER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: corner_faces *)
let C696PC_CORNER_FACES = prove
 (`forall cO sO uO vO aO.
     c977cc_normal cO sO /\ &1 < aO /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500)
     ==> &0 < sO /\ vO + aO <= cO - sO /\
         uO + aO <= &2 * cO + (&457 / &500) * sO /\
         &0 <= sO * uO + cO * vO /\
         c696cm_boundary cO sO < vO + aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C696PC_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sO = sO` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cO sO uO vO aO (&1) (&457 / &500)`) THEN
  MP_TAC(ASSUME `linside cO sO uO vO aO (&28 / &25) (&1)`) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `vO + aO <= cO - sO` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cO sO uO vO aO (&1) (&1)` THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uO + aO <= &2 * cO + (&457 / &500) * sO` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cO sO uO vO aO (&2) (&457 / &500)` THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sO * uO + cO * vO` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sO` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `sO = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C696PC_PRODLT_TAC `cO:real` `--vO` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cO * c696cm_boundary cO sO =
                cO + sO - &2 * cO * sO - (&457 / &500) * sO pow 2` ASSUME_TAC THENL
  [REWRITE_TAC[c696cm_boundary] THEN
   (SUBGOAL_THEN `~(cO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  C696PC_PROD_TAC `sO:real` `(&2 * cO + (&457 / &500) * sO) - (uO + aO)` THEN
  C696PC_PRODLT_TAC `aO - &1` `cO + sO` THEN
  MATCH_MP_TAC C977CSUP_LT_BY_POS THEN EXISTS_TAC `cO:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: relative (private) *)
let C696PC_RELATIVE = prove
 (`forall c s C TT. c977cc_normal c s /\ c977cc_normal C TT
     ==> &0 <= c * C - s * TT /\ &0 <= c * TT + s * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C696PC_NORMAL_TAC THEN
  C696PC_PROD_TAC `c:real` `C - TT` THEN
  C696PC_PROD_TAC `TT:real` `c - s` THEN
  CONJ_TAC THENL
  [NLIN_TAC ~deg2:false [];
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   RASM_ARITH_TAC]);;

(* Lean: transverse *)
let C696PC_TRANSVERSE = prove
 (`forall cO sO uO vO aO cA sA uA vA aA TT.
     sA = --TT /\ c977cc_normal cO sO /\ c977cc_normal cA TT /\ &0 < sO /\
     aO = aA /\ &1 < aA /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     vA + aA <= &2 * (cA + TT) /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> vO + aO <= ABT_lower cA sA uA vA aA (--sO) cO \/
         ABT_upper cO sO uO vO aO TT cA <= vA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sA = --TT`)) THEN
  C696PC_USE C696PC_RELATIVE [`cO:real`; `sO:real`; `cA:real`; `TT:real`] THEN
  C696PC_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1 /\ cA * cA + --TT * --TT = &1 /\ &0 < aA`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cA pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING;
    RASM_ARITH_TAC]; ALL_TAC] THEN
  let sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`]
  and sqA = [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`] in
  MP_TAC(SPECL sqA ABT_OWNV) THEN MP_TAC(SPECL sqO ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y),(nx,ny)) -> ABT_SB_TAC sq x y nx ny)
   [sqO,(`&187 / &100`,`&19 / &25`),(`cO:real`,`sO:real`);
    sqA,(`&2`,`&87 / &50`),(`cO:real`,`sO:real`);
    sqO,(`&28 / &25`,`&1`),(`cO:real`,`sO:real`);
    sqO,(`&187 / &100`,`&19 / &25`),(`cA:real`,`--TT`);
    sqA,(`&33 / &20`,`&33 / &20`),(`cA:real`,`--TT`);
    sqA,(`&2`,`&87 / &50`),(`cA:real`,`--TT`);
    sqO,(`&28 / &25`,`&1`),(`cA:real`,`--TT`);
    sqA,(`&33 / &20`,`&33 / &20`),(`--sO`,`cO:real`);
    sqO,(`&28 / &25`,`&1`),(`--sO`,`cO:real`);
    sqA,(`&33 / &20`,`&33 / &20`),(`TT:real`,`cA:real`);
    sqO,(`&28 / &25`,`&1`),(`TT:real`,`cA:real`)] THEN
  MP_TAC(ASSUME `linside cA (--TT) uA vA aA (&3 / &2) (&2)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  C696PC_PRODLT_TAC `sO:real` `cA:real` THEN
  C696PC_PROD_TAC `cO:real` `TT:real` THEN
  C696PC_USE C977NCO_LOWER_NEGATIVE_POS
    [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`; `TT:real`; `cO:real`; `sO:real`] THEN
  C696PC_USE C696CM_LONGITUDINAL [`cO:real`; `sO:real`; `cA:real`; `TT:real`] THEN
  C696PC_PROD_TAC `cO * cA - sO * TT` `(cA * &3 / &2 - TT * &2) - uA` THEN
  C696PC_PROD_TAC `cO * TT + sO * cA` `&2 * (cA + TT) - (vA + aA)` THEN
  C696PC_PRODLT_TAC `cO * TT + sO * cA` `aA - &1` THEN
  SUBGOAL_THEN
   `(cO * cA - sO * TT) * ((&3 / &2) * cA - &2 * TT) +
    (cO * TT + sO * cA) * (&2 * (cA + TT) - &1) =
    cO * (&3 / &2 + (&1 / &2) * TT pow 2 - TT) + sO * (&2 + (&1 / &2) * cA * TT - cA)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL (sqO @ sqA) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: point *)
let C696PC_POINT = prove
 (`forall cO sO uO vO aO cA sA uA vA aA cL sL uL vL aL TT.
     sA = --TT /\ c977cc_normal cO sO /\ c977cc_normal cA TT /\
     aO = aA /\ &1 < aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&1) (&87 / &50) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sA = --TT`)) THEN
  C696PC_USE C696PC_CORNER_FACES [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`] THEN
  C696PC_USE C696PC_RELATIVE [`cO:real`; `sO:real`; `cA:real`; `TT:real`] THEN
  C696PC_NORMAL_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  C977NCO_BAND_TAC `linside cA (--TT) uA vA aA (&33 / &20) (&33 / &20)` THEN
  C977NCO_BAND_TAC `linside cA (--TT) uA vA aA (&2) (&87 / &50)` THEN
  C977NCO_BAND_TAC `linside cA (--TT) uA vA aA (&87 / &50) (&2)` THEN
  SUBGOAL_THEN `vA + aA <= &2 * (cA + TT)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cA (--TT) uA vA aA (&2) (&2)` THEN
   REWRITE_TAC[C977NCO_NEG_BANDS] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < TT` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C696PC_PRODLT_TAC `sO:real` `cA:real` THEN
  C696PC_PROD_TAC `cO:real` `TT:real` THEN
  SUBGOAL_THEN `vO + aA <= (--(cO * TT + sO * cA) * (uA + aA) + (cO * cA - sO * TT) * vA)` ASSUME_TAC THENL
  [MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`;
                 `cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`; `TT:real`]
     C696PC_TRANSVERSE) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
   STRIP_TAC THENL
   [C696PC_USE C977NCO_LOWER_NEGATIVE_NONPOS
      [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`; `TT:real`; `--sO`; `cO:real`] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
   C696PC_USE C696PC_UPPER_PP
     [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`; `TT:real`; `cA:real`] THEN
   C696PC_USE C696CM_CENTRAL_AXIS [`cO:real`; `sO:real`; `cA:real`; `TT:real`] THEN
   SUBGOAL_THEN `&0 <= cO * sO` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(cO * sO) * (&2 * (cA + TT)) <=
                 cO * TT * (&1 - cO + sO) + (cO * sO) * ((cO * TT + sO * cA) + (cO * cA - sO * TT) + &1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `cO * TT * (&1 - cO + sO) + (cO * sO) * ((cO * TT + sO * cA) + (cO * cA - sO * TT) + &1) =
                  (cO * sO) * ((TT / sO) * (&1 - cO + sO) + (cO * TT + sO * cA) +
                               (cO * cA - sO * TT) + &1)` SUBST1_TAC THENL
    [(SUBGOAL_THEN `~(sO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
     CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(cO * sO) * (vA + aA) <= (cO * sO) * (&2 * (cA + TT))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_upper c s u v a nx ny = e`) (concl th)
                           then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
   SUBGOAL_THEN `(cO * sO) * ((TT * cO + cA * sO) * (uO + aA) +
                              (--TT * sO + cA * cO) * (vO + aA)) <= (cO * sO) * vA`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   C696PC_PROD_TAC `cO:real` `(cO - sO) - (vO + aA)` THEN
   SUBGOAL_THEN `&0 <= sO * uO - cO * (aA - cO + sO)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   C696PC_PROD_TAC `TT:real` `sO * uO - cO * (aA - cO + sO)` THEN
   SUBGOAL_THEN `&0 <= sO * (cO * cA - sO * TT)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
   C696PC_PROD_TAC `sO * (cO * cA - sO * TT)` `sO * uO + cO * vO` THEN
   SUBGOAL_THEN `&0 < sO * ((cO * TT + sO * cA) + (cO * cA - sO * TT) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
   C696PC_PRODLT_TAC `cO:real` `TT + sO * ((cO * TT + sO * cA) + (cO * cA - sO * TT) + &1)` THEN
   C696PC_PRODLT_TAC `aA - &1` `cO * (TT + sO * ((cO * TT + sO * cA) + (cO * cA - sO * TT) + &1))` THEN
   SUBGOAL_THEN
    `(cO * sO) * (((TT * cO + cA * sO) * (uO + aA) +
                   (--TT * sO + cA * cO) * (vO + aA)) + aA) =
     sO * TT * uO + (sO * (cO * cA - sO * TT)) * (sO * uO + cO * vO) + aA * (cO * sO) * ((cO * TT + sO * cA) + (cO * cA - sO * TT) + &1)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `c696cm_boundary cO sO < (--(cO * TT + sO * cA) * (uA + aA) + (cO * cA - sO * TT) * vA)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  (* left *)
  SUBGOAL_THEN `cA * uA + TT * vA < &1` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C696PC_PROD_TAC `(cO * TT + sO * cA)` `(cA * uA + TT * vA) - &1` THEN
   C696PC_PROD_TAC `cO:real` `&2 * (cA + TT) - (vA + aA)` THEN
   C696PC_PROD_TAC `cA:real` `(cO * TT + sO * cA)` THEN
   C696PC_PRODLT_TAC `aA - &1` `cO + cA * (cO * TT + sO * cA)` THEN
   SUBGOAL_THEN `cA * (--(cO * TT + sO * cA) * (uA + aA) + (cO * cA - sO * TT) * vA) = cO * vA - (cO * TT + sO * cA) * (cA * uA + TT * vA) - cA * (cO * TT + sO * cA) * aA`
   ASSUME_TAC THENL
   [UNDISCH_TAC `cA pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C696PC_USE C696CM_LEFT_COMPARISON [`cO:real`; `sO:real`; `cA:real`; `TT:real`] THEN
   SUBGOAL_THEN `cO * (&2 * (cA + TT) - &1) - (cO * TT + sO * cA) - cA * (cO * TT + sO * cA) <=
                 cA * c696cm_boundary cO sO` ASSUME_TAC THENL
   [SUBGOAL_THEN `cO * (&2 * (cA + TT) - &1) - (cO * TT + sO * cA) - cA * (cO * TT + sO * cA) =
                  cA * (cO * (&2 + (TT - &1) / cA - TT) - sO * (&1 + cA))` SUBST1_TAC THENL
    [(SUBGOAL_THEN `~(cA = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
     CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `cA * c696cm_boundary cO sO < cA * (--(cO * TT + sO * cA) * (uA + aA) + (cO * cA - sO * TT) * vA)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  (* near *)
  SUBGOAL_THEN `uA < cA - (&28 / &25) * TT` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C696PC_PROD_TAC `(cO * TT + sO * cA)` `uA - (cA - (&28 / &25) * TT)` THEN
   C696PC_PROD_TAC `(cO * cA - sO * TT)` `&2 * (cA + TT) - (vA + aA)` THEN
   C696PC_PRODLT_TAC `aA - &1` `(cO * TT + sO * cA) + (cO * cA - sO * TT)` THEN
   SUBGOAL_THEN
    `--(cO * TT + sO * cA) * (cA - (&28 / &25) * TT + &1) + (cO * cA - sO * TT) * (&2 * (cA + TT) - &1) =
     cO * (&2 - (&22 / &25) * TT pow 2 + cA * TT - cA - TT) -
     sO * (&1 + TT pow 2 + (&22 / &25) * cA * TT + cA - TT)` ASSUME_TAC THENL
   [UNDISCH_TAC `cA pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C696PC_USE C696CM_NEAR_COMPARISON [`cO:real`; `sO:real`; `cA:real`; `TT:real`] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  C696PC_USE C977NCO_FOREIGN_SEGMENT_OVERLAP
    [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`;
     `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `TT:real`] THEN
  UNDISCH_TAC `ldisj cA (--TT) uA vA aA cL sL uL vL aL` THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[]);;
