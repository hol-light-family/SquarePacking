(* ========================================================================= *)
(* Port of Compact/Geometry/CentralSteeperNegativeBottom.lean (Jatloe,       *)
(* N12-jatloe; namespace N12Compact.CentralSteeperNegativeBottom).  The      *)
(* small upper-U excess forced by the actual steeper southeast neighbour     *)
(* still excludes a steep negative bottom singleton.  Normal is              *)
(* c977cc_normal; boundary c977cc_boundary; lower / upper ABT_lower /        *)
(* ABT_upper; strict_bounds ABT_STRICT_BOUNDS (ABT_SB_TAC); ownU / ownV      *)
(* ABT_OWNU / ABT_OWNV; CongruentSAT.faceSeparation_of_disjoint with         *)
(* separated / parallel_radius / transverse_radius is ABT_FOUR_AXES;         *)
(* corner_face C977NCO_CORNER_FACE; negative_bands C977NCO_NEGATIVE_BANDS;   *)
(* OwnedWestBottomAngle.upper_v_spread / central_axis_impossible             *)
(* OWBA_UPPER_V_SPREAD / OWBA_CENTRAL_AXIS_IMPOSSIBLE.  A square O with      *)
(* O.s = -t is cO sO uO vO aO with sO = --t; the Lean abbreviations Q, R are *)
(* variables with their defining equations, H, K are written out.  The      *)
(* OpenSquare invariants are explicit hypotheses.  Tag CSNB_.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/OwnedWestBottomAngle.ml";;

let CSNB_PROD = PCT_PROD_TAC;;

(* Lean: transverse (private) *)
let CSNB_TRANSVERSE = prove
 (`forall cO sO uO vO aO cA sA uA vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\
     aO = aA /\ &1 < aA /\ sA <= &2 / &5 /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     uA + aA <= &2 * (cA + sA) + (&9 / &100) * cA /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> vO + aO <= ABT_lower cA sA uA vA aA t cO \/
         ABT_upper cO sO uO vO aO (--sA) cA <= vA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  PCT_NORMAL_TAC THEN
  let sqO = [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`]
  and sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL (sqO @ sqA) ABT_FOUR_AXES)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL sqO ABT_OWNV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL sqA ABT_OWNU) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL sqA ABT_OWNV) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun (sq,(x,y),(nx,ny)) -> ABT_SB_TAC sq x y nx ny)
   [sqO,(`&187 / &100`,`&19 / &25`),(`cO:real`,`--t`);
    sqA,(`&33 / &20`,`&33 / &20`),(`cO:real`,`--t`);
    sqO,(`&28 / &25`,`&1`),(`cO:real`,`--t`);
    sqA,(`&2`,`&87 / &50`),(`cO:real`,`--t`);
    sqA,(`&33 / &20`,`&33 / &20`),(`t:real`,`cO:real`);
    sqO,(`&28 / &25`,`&1`),(`t:real`,`cO:real`);
    sqO,(`&187 / &100`,`&19 / &25`),(`cA:real`,`sA:real`);
    sqO,(`&28 / &25`,`&1`),(`cA:real`,`sA:real`);
    sqA,(`&2`,`&87 / &50`),(`cA:real`,`sA:real`);
    sqA,(`&33 / &20`,`&33 / &20`),(`--sA`,`cA:real`);
    sqO,(`&28 / &25`,`&1`),(`--sA`,`cA:real`)] THEN
  REPEAT STRIP_TAC THEN ABT_ARITH_TAC);;

(* Lean: remainder (private) *)
let CSNB_REMAINDER = prove
 (`forall c t C S. c977cc_normal c t /\ c977cc_normal C S /\ S <= &2 / &5
     ==> (c + t) * ((&1 - C) - (&7 / &20) * S pow 2) - (c - t) * S * (&1 - (&7 / &20) * C) +
         (&9 / &100) * C * (t * C + c * S) <= (&9 / &100) * t \/
         (c + t) * ((&1 - C) - (&7 / &20) * S pow 2) - (c - t) * S * (&1 - (&7 / &20) * C) +
         (&9 / &100) * C * (t * C + c * S) <= (&3593 / &9500) * t - (&93 / &475) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&9 / &10 <= C` ASSUME_TAC THENL
  [CSNB_PROD `&2 / &5 - S` `S + &2 / &5` THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   CSNB_PROD `&9 / &10 - C` `&9 / &10 + C` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CSNB_PROD `&1 - C` `(&10 / &19) * (&1 + C) - &1` THEN
  SUBGOAL_THEN `&1 - C <= (&10 / &19) * S pow 2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CSNB_PROD `c + t` `(&10 / &19) * S pow 2 - (&1 - C)` THEN
  CSNB_PROD `c - t` `S:real` THEN
  CSNB_PROD `(c - t) * S` `&1 - (&7 / &20) * C - &13 / &20` THEN
  CSNB_PROD `S:real` `&2 / &5 - S` THEN
  CSNB_PROD `c + t` `S * (&2 / &5 - S)` THEN
  MP_TAC(SPECL [`t:real`; `S pow 2`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  CSNB_PROD `c:real` `S:real` THEN
  CSNB_PROD `c * S` `&1 - C` THEN
  SUBGOAL_THEN `t * C pow 2 + t * S pow 2 = t` ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `exists Q. Q = --(&93 / &190) * c + (&1369 / &1900) * t` (X_CHOOSE_TAC `Q:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(c + t) * ((&1 - C) - (&7 / &20) * S pow 2) - (c - t) * S * (&1 - (&7 / &20) * C) +
    (&9 / &100) * C * (t * C + c * S) <= (&9 / &100) * t + S * Q` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `Q <= &0` THENL
  [DISJ1_TAC THEN CSNB_PROD `S:real` `--Q` THEN NLIN_TAC ~deg2:false [];
   DISJ2_TAC THEN CSNB_PROD `Q:real` `&2 / &5 - S` THEN
   UNDISCH_TAC `Q = --(&93 / &190) * c + (&1369 / &1900) * t` THEN
   DISCH_THEN SUBST_ALL_TAC THEN NLIN_TAC ~deg2:false []]);;

(* Lean: own_axis_impossible (private) *)
let CSNB_OWN_AXIS_IMPOSSIBLE = prove
 (`forall cO (sO:real) (uO:real) vO aO cA sA uA vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO t /\ c977cc_normal cA sA /\
     &1 <= aA /\ sA <= &2 / &5 /\ &47 / &100 < t /\ &27 / &20 < cO + t /\
     uA + aA <= &2 * (cA + sA) + (&9 / &100) * cA /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     c977cc_boundary cO t < vO + aO /\
     vO + aO <= ABT_lower cA sA uA vA aA t cO
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `t:real`; `cA:real`; `sA:real`] CSNB_REMAINDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists R. R = (cO + t) * ((&1 - cA) - (&7 / &20) * sA pow 2) -
                        (cO - t) * sA * (&1 - (&7 / &20) * cA) +
                        (&9 / &100) * cA * (t * cA + cO * sA)` (X_CHOOSE_TAC `R:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_disj (concl th) then
    ASSUME_TAC(REWRITE_RULE[SYM(ASSUME `R = (cO + t) * ((&1 - cA) - (&7 / &20) * sA pow 2) -
                        (cO - t) * sA * (&1 - (&7 / &20) * cA) +
                        (&9 / &100) * cA * (t * cA + cO * sA)`)] th) else failwith "") THEN
  CSNB_PROD `t:real` `cA:real` THEN CSNB_PROD `cO:real` `sA:real` THEN
  CSNB_PROD `cO:real` `cA - sA:real` THEN CSNB_PROD `sA:real` `cO - t:real` THEN
  SUBGOAL_THEN `&0 <= t * cA + cO * sA /\ &0 <= cO * cA - t * sA` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `t:real`; `cO:real`] PCT_LOWER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  CSNB_PROD `t * cA + cO * sA` `(&2 * (cA + sA) + (&9 / &100) * cA) - (uA + aA)` THEN
  CSNB_PROD `cO * cA - t * sA` `((&47 / &20) * cA - (&33 / &20) * sA) - (vA + aA)` THEN
  CSNB_PROD `aA - &1` `(t * cA + cO * sA) + (cO * cA - t * sA)` THEN
  SUBGOAL_THEN
   `(t * cA + cO * sA) * (&2 * (cA + sA) + (&9 / &100) * cA) +
    (cO * cA - t * sA) * ((&47 / &20) * cA - (&33 / &20) * sA) -
    (t * cA + cO * sA) - (cO * cA - t * sA) = t + (&27 / &20) * cO + R` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `(t * cA + cO * sA) * uA + (--t * sA + cO * cA) * vA <= t + (&27 / &20) * cO + R`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `t:real`] OWBA_BOUNDARY_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cO * (c977cc_boundary cO t - (t + (&27 / &20) * cO + R))` ASSUME_TAC THENL
  [FIRST_X_ASSUM(fun th -> if is_disj (concl th) then DISJ_CASES_TAC th else failwith "") THENL
   [CSNB_PROD `t:real` `(&7 / &20) * t - (&9 / &100) * cO` THEN
    CSNB_PROD `cO:real` `(&9 / &100) * t - R` THEN
    NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `cO * t <= &1 / &2` ASSUME_TAC THENL
    [NLIN_TAC [SQ_NONNEG `cO - t:real`]; ALL_TAC] THEN
    CSNB_PROD `cO:real` `(&3593 / &9500) * t - (&93 / &475) * cO - R` THEN
    NLIN_TAC ~deg2:false [SPEC `t:real` REAL_LE_POW_2]];
   ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `c977cc_boundary cO t - (t + (&27 / &20) * cO + R)`]
    PCT_POS_BY_POS) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: small_bottom *)
let CSNB_SMALL_BOTTOM = prove
 (`forall cO sO uO vO aO cA sA uA vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\
     aO = aA /\ &1 < aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     sA <= &2 / &5 /\ uA + aA <= &2 * (cA + sA) + (&9 / &100) * cA /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> t < &1 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`] CSNB_TRANSVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`; `t:real`]
    C977NCO_CORNER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uO + aA <= &2 * cO - (&457 / &500) * t \/
                vO + aA <= &2 * t + (&457 / &500) * cO` MP_TAC THENL
  [UNDISCH_TAC `~linside cO (--t) uO vO aA (&2) (&457 / &500)` THEN
   UNDISCH_TAC `linside cO (--t) uO vO aA (&1) (&457 / &500)` THEN
   REWRITE_TAC[linside] THEN STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
  [SUBGOAL_THEN `&1 - cO < (&43 / &500) * t` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   OWBA_PRODLT `&1 + cO` `(&43 / &500) * t - (&1 - cO)` THEN
   OWBA_PROD `t:real` `&1 - cO` THEN
   SUBGOAL_THEN `t pow 2 < (&43 / &250) * t` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`t:real`; `&43 / &250 - t`] PCT_POS_BY_POS) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `t:real`] OWBA_UPPER_V_SPREAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_disj (concl th) && free_in `ABT_lower cA sA uA vA aA t cO` (concl th)
                          then DISJ_CASES_TAC th else failwith "") THENL
  [MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`;
                 `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`] CSNB_OWN_AXIS_IMPOSSIBLE) THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
   REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
   MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`;
                 `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`] OWBA_CENTRAL_AXIS_IMPOSSIBLE) THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
   REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC)]);;
