(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ThreeCentral/SteepSupport.lean      *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(*  N12Compact.Completion.OtherCases.ThreeCentral).                          *)
(* The southwest support argument for every positive normal above the        *)
(* diagonal.  Lean upper is ABT_upper; C868CentralSupport.modes is           *)
(* C868CS_MODES.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C868CentralSupport.ml";;

let OC3CSS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let OC3CSS_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let OC3CSS_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let OC3CSS_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let OC3CSS_UPPER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: normal_coarse (private) *)
let OC3CSS_NORMAL_COARSE = prove
 (`forall C S. c977cc_normal C S
     ==> &7 / &10 <= C /\ C <= &1 /\ &0 <= S /\ S <= &3 / &4 /\
         &1 <= C + S /\ C + S <= &17 / &12 /\ C * S <= &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN OC3CSS_NORMAL_TAC THEN
  OC3CSS_PROD_TAC `C - S` `C + S` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `S - &3 / &4`; SQ_NONNEG `C - S:real`; SQ_NONNEG `C + S - &17 / &12`]);;

(* Lean: steep_linear (private) *)
let OC3CSS_STEEP_LINEAR = prove
 (`forall c s p q. &0 <= c /\ c <= s /\ &0 <= p + q /\ &0 <= q ==> &0 <= c * p + s * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OC3CSS_PROD_TAC `c:real` `p + q` THEN OC3CSS_PROD_TAC `s - c` `q:real` THEN
  NLIN_TAC ~deg2:false []);;

let OC3CSS_STEEP_FINISH_TAC p q =
  MP_TAC(SPECL [`c:real`; `s:real`; p; q] OC3CSS_STEEP_LINEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;;

(* Lean: steep_I (private) *)
let OC3CSS_STEEP_I = prove
 (`forall c s C S. c977cc_normal C S /\ &0 <= c /\ c <= s
     ==> &0 <= (c * C + s * S) * (&1 + (&8 / &5) * C + S) +
               (s * C - c * S) * (&2 * C - (&87 / &50) * S) -
               (&47 / &20) * c - (&33 / &20) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OC3CSS_USE OC3CSS_NORMAL_COARSE [`C:real`; `S:real`] THEN OC3CSS_NORMAL_TAC THEN
  OC3CSS_PROD_TAC `C - S` `C + S` THEN
  NLIN_FACTS_TAC [] [`S pow 2 <= &1 / &2`] THEN
  OC3CSS_PROD_TAC `&3 / &2 - (C + S)` `(C + S) - &1` THEN
  NLIN_FACTS_TAC [] [`&1 + (&4 / &5) * C * S <= C + S`] THEN
  SUBGOAL_THEN
   `&0 <= (C + (&8 / &5) * C pow 2 + (&87 / &50) * S pow 2 - C * S - &47 / &20) +
          (S + &2 * C pow 2 + S pow 2 - (&7 / &50) * C * S - &33 / &20)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  OC3CSS_PROD_TAC `S:real` `&1 - S - (&7 / &50) * C` THEN
  SUBGOAL_THEN `&0 <= S + &2 * C pow 2 + S pow 2 - (&7 / &50) * C * S - &33 / &20`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  OC3CSS_STEEP_FINISH_TAC
    `C + (&8 / &5) * C pow 2 + (&87 / &50) * S pow 2 - C * S - &47 / &20`
    `S + &2 * C pow 2 + S pow 2 - (&7 / &50) * C * S - &33 / &20`);;

(* Lean: steep_II (private) *)
let OC3CSS_STEEP_II = prove
 (`forall c s C S. c977cc_normal C S /\ &0 <= c /\ c <= s /\ &13 * S <= C
     ==> &0 <= (c * C + s * S) * (&2 * C + (&87 / &50) * S) +
               (s * C - c * S) * (&1 + (&8 / &5) * C - S) -
               (&47 / &20) * c - (&33 / &20) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OC3CSS_USE OC3CSS_NORMAL_COARSE [`C:real`; `S:real`] THEN OC3CSS_NORMAL_TAC THEN
  SUBGOAL_THEN `S <= &1 / &13` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  OC3CSS_PROD_TAC `S:real` `&1 / &13 - S` THEN
  NLIN_FACTS_TAC [] [`S pow 2 <= &1 / &169`] THEN
  SUBGOAL_THEN `&9 / &10 <= C` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   OC3CSS_PROD_TAC `C:real` `&9 / &10 - C` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  OC3CSS_PROD_TAC `C:real` `S:real` THEN
  SUBGOAL_THEN
   `&0 <= (&2 * C pow 2 + (&7 / &50) * C * S + S pow 2 - S - &47 / &20) +
          (C + (&8 / &5) * C pow 2 + (&87 / &50) * S pow 2 + C * S - &33 / &20) /\
    &0 <= C + (&8 / &5) * C pow 2 + (&87 / &50) * S pow 2 + C * S - &33 / &20`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `S:real`]; ALL_TAC] THEN
  OC3CSS_STEEP_FINISH_TAC
    `&2 * C pow 2 + (&7 / &50) * C * S + S pow 2 - S - &47 / &20`
    `C + (&8 / &5) * C pow 2 + (&87 / &50) * S pow 2 + C * S - &33 / &20`);;

(* Lean: steep_III (private) *)
let OC3CSS_STEEP_III = prove
 (`forall c s C S. c977cc_normal C S /\ &0 <= c /\ c <= s
     ==> &0 <= (c * C + s * S) * (&1 + C + (&8 / &5) * S) +
               (s * C - c * S) * (&1 + C - (&8 / &5) * S) -
               (&47 / &20) * c - (&33 / &20) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OC3CSS_USE OC3CSS_NORMAL_COARSE [`C:real`; `S:real`] THEN OC3CSS_NORMAL_TAC THEN
  OC3CSS_PROD_TAC `&1 - C` `(&6 / &5) * C - &4 / &5` THEN
  SUBGOAL_THEN
   `&0 <= (C - S + C pow 2 + (&3 / &5) * C * S + (&8 / &5) * S pow 2 - &47 / &20) +
          (C + S + C pow 2 - (&3 / &5) * C * S + (&8 / &5) * S pow 2 - &33 / &20) /\
    &0 <= C + S + C pow 2 - (&3 / &5) * C * S + (&8 / &5) * S pow 2 - &33 / &20`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `S:real`]; ALL_TAC] THEN
  OC3CSS_STEEP_FINISH_TAC
    `C - S + C pow 2 + (&3 / &5) * C * S + (&8 / &5) * S pow 2 - &47 / &20`
    `C + S + C pow 2 - (&3 / &5) * C * S + (&8 / &5) * S pow 2 - &33 / &20`);;

(* Lean: steep_support *)
let OC3CSS_STEEP_SUPPORT = prove
 (`forall cA sA uA vA aA c s.
     c977cc_normal cA sA /\ &0 < c /\ c <= s /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\ linside cA sA uA vA aA (&87 / &50) (&2) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\ ~linside cA sA uA vA aA (&1) (&8 / &5)
     ==> (&47 / &20) * c + (&33 / &20) * s < ABT_upper cA sA uA vA aA c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC3CSS_NORMAL_TAC THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] C868CS_MODES) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC] THEN
  OC3CSS_PRODLT_TAC `c:real` `cA:real` THEN OC3CSS_PROD_TAC `s:real` `sA:real` THEN
  OC3CSS_PROD_TAC `s - c` `cA:real` THEN OC3CSS_PROD_TAC `c:real` `cA - sA` THEN
  SUBGOAL_THEN `&0 < c * cA + s * sA /\ &0 <= s * cA - c * sA` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  OC3CSS_USE OC3CSS_UPPER_PP
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `c:real`; `s:real`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&2) (&87 / &50)`) THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&87 / &50) (&2)`) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  OC3CSS_PRODLT_TAC `c * cA + s * sA` `aA - &1` THEN
  OC3CSS_PROD_TAC `s * cA - c * sA` `aA - &1` THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
  [OC3CSS_USE OC3CSS_STEEP_I [`c:real`; `s:real`; `cA:real`; `sA:real`] THEN
   OC3CSS_PROD_TAC `c * cA + s * sA` `uA - ((&8 / &5) * cA + sA)` THEN
   OC3CSS_PROD_TAC `s * cA - c * sA` `(vA + aA) - (cA * &2 - sA * &87 / &50)` THEN
   NLIN_TAC ~deg2:false [];
   OC3CSS_USE OC3CSS_STEEP_II [`c:real`; `s:real`; `cA:real`; `sA:real`] THEN
   OC3CSS_PRODLT_TAC `c * cA + s * sA` `(uA + aA) - (cA * &2 + sA * &87 / &50)` THEN
   OC3CSS_PROD_TAC `s * cA - c * sA` `vA - ((&8 / &5) * cA - sA)` THEN
   NLIN_TAC ~deg2:false [];
   OC3CSS_USE OC3CSS_STEEP_III [`c:real`; `s:real`; `cA:real`; `sA:real`] THEN
   OC3CSS_PROD_TAC `c * cA + s * sA` `uA - (cA + (&8 / &5) * sA)` THEN
   OC3CSS_PROD_TAC `s * cA - c * sA` `vA - (cA - (&8 / &5) * sA)` THEN
   NLIN_TAC ~deg2:false []]);;
