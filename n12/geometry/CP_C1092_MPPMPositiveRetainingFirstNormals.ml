(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveRetainingFirstNormals.lean   *)
(* (N12Compact.C1092MPPMPositiveRetainingFirstNormals).  POSITIVE-RETAINING- *)
(* FIRST-NORMALS Theorem 1.  Squares C = cC sC uC vC aC, E = cE sE uE vE aE. *)
(* upper/lower: ABT_upper/ABT_lower; formulas: C1092WS_FORMULAS; scalar      *)
(* lemmas: C1092PRFN_*; Normal is c977cc_normal.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingFirstNormalsScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* REAL_ARITH from the listed assumptions only *)
let C1092PRFNT_ARITH_WITH tms (asl,w as g) =
  let ths = map (fun t ->
    try snd(find (fun (_,th) -> aconv (concl th) t) asl)
    with Failure _ -> failwith ("C1092PRFNT_ARITH_WITH: missing " ^ string_of_term t)) tms in
  (MAP_EVERY MP_TAC ths THEN REAL_ARITH_TAC) g;;

(* Lean: Input (structure) *)
let c1092prfnt_input = new_definition
 `c1092prfnt_input cC sC uC vC aC cE sE (uE:real) vE aE <=>
    &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ c977cc_normal cE sE /\
    aC - cC - sC <= uC + aC /\ uC + aC <= &0 /\ vC + aC <= sC /\
    --(&13 / &50) * cE < vE + aE /\ &0 < --uE /\ --uE <= sE`;;

(* Lean: upper_opposite (private) *)
let C1092PRFNT_UPPER_OPPOSITE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a ==> ABT_upper c s u v a s (--c) = --v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `s:real`; `--c:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `s * c + --c * s = &0 /\ --s * s + --c * c = -- &1` (fun th -> REWRITE_TAC[th])
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `max (&0) (&0) = &0 /\ max (-- &1) (&0) = &0`] THEN REAL_ARITH_TAC);;

(* Lean: lower_opposite (private) *)
let C1092PRFNT_LOWER_OPPOSITE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a ==> ABT_lower c s u v a s (--c) = --(v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `s:real`; `--c:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `s * c + --c * s = &0 /\ --s * s + --c * c = -- &1` (fun th -> REWRITE_TAC[th])
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `min (&0) (&0) = &0 /\ min (-- &1) (&0) = -- &1`] THEN REAL_ARITH_TAC);;

let C1092PRFNT_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092prfnt_input] o
    check (fun th -> can (term_match [] `c1092prfnt_input a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092PRFN_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: transverse_C *)
let C1092PRFNT_TRANSVERSE_C = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prfnt_input cC sC uC vC aC cE sE uE vE aE
     ==> ~(ABT_upper cC sC uC vC aC sC (--cC) <= ABT_lower cE sE uE vE aE sC (--cC))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRFNT_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092PRFN_TRANSVERSE_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[C1092PRFNT_UPPER_OPPOSITE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `sC * cE + --cC * sE = --(cC * sE - sC * cE) /\
                --sC * sE + --cC * cE = --(cC * cE + sC * sE)` (fun th -> REWRITE_TAC[th])
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (cC * cE + sC * sE) * (vE + aC + (&13 / &50) * cE)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `min (--(cC * cE + sC * sE)) (&0) = --(cC * cE + sC * sE)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
  [SUBGOAL_THEN `min (--(cC * sE - sC * cE)) (&0) = --(cC * sE - sC * cE)`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
     check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
   SUBGOAL_THEN `&0 <= (cC * sE - sC * cE) * (sE - --uE) /\
                 &0 <= (cC * sE - sC * cE) * (&1 - sE) /\
                 &0 < (aC - &1) * (&1 + (cC * sE - sC * cE))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   C1092PRFNT_ARITH_WITH
    [`ABT_lower cE sE uE vE aC sC (--cC) =
      --(cC * sE - sC * cE) * uE + --(cC * cE + sC * sE) * vE +
      aC * --(cC * sE - sC * cE) + aC * --(cC * cE + sC * sE)`;
     `--vC <= ABT_lower cE sE uE vE aC sC (--cC)`;
     `&0 <= (cC * sE - sC * cE) * (sE - --uE)`;
     `&0 <= (cC * sE - sC * cE) * (&1 - sE)`;
     `&0 < (aC - &1) * (&1 + (cC * sE - sC * cE))`;
     `&0 < (cC * cE + sC * sE) * (vE + aC + (&13 / &50) * cE)`;
     `vC + aC <= sC`;
     `sC + (&13 / &50) * (cC * cE + sC * sE) * cE < &1`];
   SUBGOAL_THEN `min (--(cC * sE - sC * cE)) (&0) = &0`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `&0 <= --(cC * sE - sC * cE) * --uE` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C1092PRFNT_ARITH_WITH
    [`ABT_lower cE sE uE vE aC sC (--cC) =
      --(cC * sE - sC * cE) * uE + --(cC * cE + sC * sE) * vE +
      aC * &0 + aC * --(cC * cE + sC * sE)`;
     `--vC <= ABT_lower cE sE uE vE aC sC (--cC)`;
     `&0 <= --(cC * sE - sC * cE) * --uE`;
     `&0 < (cC * cE + sC * sE) * (vE + aC + (&13 / &50) * cE)`;
     `vC + aC <= sC`; `&1 < aC`;
     `sC + (&13 / &50) * (cC * cE + sC * sE) * cE < &1`]]);;

(* Lean: transverse_E *)
let C1092PRFNT_TRANSVERSE_E = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prfnt_input cC sC uC vC aC cE sE uE vE aE
     ==> ~(ABT_upper cC sC uC vC aC sE (--cE) <= ABT_lower cE sE uE vE aE sE (--cE))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRFNT_SETUP_TAC THEN
  ASM_SIMP_TAC[C1092PRFNT_LOWER_OPPOSITE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `sE * cC + --cE * sC = cC * sE - sC * cE /\
                --sE * sC + --cE * cC = --(cC * cE + sC * sE)` (fun th -> REWRITE_TAC[th])
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `max (--(cC * cE + sC * sE)) (&0) = &0`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (cC * cE + sC * sE) * (sC - (vC + aC))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
  [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092PRFN_SUCCESSOR_UP) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (cC * sE - sC * cE) * ((uC + aC) - (aC - cC - sC)) /\
                 &0 < (aC - &1) * ((cC * cE + sC * sE) + (cC * sE - sC * cE))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   C1092PRFNT_ARITH_WITH
    [`ABT_upper cC sC uC vC aC sE (--cE) =
      (cC * sE - sC * cE) * uC + --(cC * cE + sC * sE) * vC +
      aC * (cC * sE - sC * cE) + aC * &0`;
     `ABT_upper cC sC uC vC aC sE (--cE) <= --(vE + aC)`;
     `&0 <= (cC * cE + sC * sE) * (sC - (vC + aC))`;
     `&0 <= (cC * sE - sC * cE) * ((uC + aC) - (aC - cC - sC))`;
     `&0 < (aC - &1) * ((cC * cE + sC * sE) + (cC * sE - sC * cE))`;
     `--(&13 / &50) * cE < vE + aC`;
     `(cC * cE + sC * sE) * (sC - &1) + (cC * sE - sC * cE) * (cC + sC - &1) +
      (&13 / &50) * cE < &0`];
   SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> max x (&0) = &0`] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092PRFN_SUCCESSOR_DOWN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= --(cC * sE - sC * cE) * --(uC + aC) /\
                 &0 < (aC - &1) * ((cC * cE + sC * sE) - (cC * sE - sC * cE))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   C1092PRFNT_ARITH_WITH
    [`ABT_upper cC sC uC vC aC sE (--cE) =
      (cC * sE - sC * cE) * uC + --(cC * cE + sC * sE) * vC + aC * &0 + aC * &0`;
     `ABT_upper cC sC uC vC aC sE (--cE) <= --(vE + aC)`;
     `&0 <= (cC * cE + sC * sE) * (sC - (vC + aC))`;
     `&0 <= --(cC * sE - sC * cE) * --(uC + aC)`;
     `&0 < (aC - &1) * ((cC * cE + sC * sE) - (cC * sE - sC * cE))`;
     `--(&13 / &50) * cE < vE + aC`;
     `(cC * cE + sC * sE) * (sC - &1) + (cC * sE - sC * cE) + (&13 / &50) * cE < &0`]]);;
