(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallOppositeAxes.lean                     *)
(*                                                                           *)
(* Narrow elbow A = (cA, sA, uA, vA, aA), opposite square D with sD = --S.   *)
(* lower/upper are ABT_lower/ABT_upper; the support forms of                 *)
(* C981.SupportForms (lower_in_bands, upper_in_bands) are                    *)
(* C977NCO_LOWER_IN_BANDS / C977NCO_UPPER_IN_BANDS.  The four-axis case      *)
(* split (faceSeparation_of_disjoint + separated) is ABT_FOUR_AXES.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/FullAuxWallLowerCorner.ml";;

let FAWOA_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
     REWRITE_TAC[lcont; ldisj; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

let FAWOA_STRIP_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC));;

(* Lean: opposite_u_impossible (private) *)
let FAWOA_OPPOSITE_U_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD S.
     cA * cA + sA * sA = &1 /\
     &0 < cA /\ &0 < sA /\ &4 * sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     sD = --S /\ &0 < cD /\ &0 <= S /\ S <= cD /\
     linside cD sD uD vD aD (&2) (&2) /\
     uD + aD <= ABT_lower cA sA uA vA aA cD sD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sD = --S` o concl)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cA sA uA vA aA (&5 / &2) (&3)`;
    `linside cD (--S) uD vD aD (&2) (&2)`] THEN
  NLIN_FACTS_TAC [] [`&0 < cA * cD - sA * S`; `&0 < cA * S + sA * cD`] THEN
  SUBGOAL_THEN `ABT_lower cA sA uA vA aA cD (--S) =
                (cA * cD - sA * S) * uA - (cA * S + sA * cD) * (vA + aA)` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cD * cA + --S * sA) = cA * cD - sA * S /\
                  abs(--cD * sA + --S * cA) = cA * S + sA * cD`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(cA * cD - sA * S) * uA - (cA * S + sA * cD) * (vA + aA) - &2 * (cD - S) =
                (cA * cD - sA * S) * (uA - &2 * (cA + sA)) -
                (cA * S + sA * cD) * (vA + aA - &2 * (cA - sA))` ASSUME_TAC THENL
   [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`(cA * cD - sA * S) * (uA - &2 * (cA + sA)) < (cA * cD - sA * S) * ((&13 / &50) * sA)`;
    `(cA * S + sA * cD) * (cA - sA / &2) < (cA * S + sA * cD) * (vA + aA - &2 * (cA - sA))`;
    `&0 < cD * sA * ((&37 / &50) * cA - sA / &2)`;
    `&0 <= cA * (cA - sA / &2)`;
    `&0 <= S * (cA pow 2 - cA * sA / &2 + (&13 / &50) * sA pow 2)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cA sA uA vA aA cD (--S) =
                (cA * cD - sA * S) * uA - (cA * S + sA * cD) * (vA + aA)`]) THEN
  NLIN_TAC []);;


(* Lean: separation *)
let FAWOA_SEPARATION = prove
 (`forall cA sA uA vA aA cD sD uD vD aD S.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aA /\ aA = aD /\
     &0 < cA /\ &0 < sA /\ &4 * sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     sD = --S /\ &0 < cD /\ &0 <= S /\ S <= cD /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&2) (&2) /\
     ldisj cA sA uA vA aA cD sD uD vD aD
     ==> ABT_upper cD sD uD vD aD cA sA <= uA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aD` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sD = --S` o concl)) THEN
  SUBGOAL_THEN `~(uD + aA <= ABT_lower cA sA uA vA aA cD (--S))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FAWOA_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cD:real`; `--S:real`; `uD:real`; `vD:real`; `aA:real`; `S:real`]
      FAWOA_OPPOSITE_U_IMPOSSIBLE) THEN
    FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(vD + aA <= ABT_lower cA sA uA vA aA (-- --S) cD)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FAWOA_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cD:real`; `--S:real`; `uD:real`; `vD:real`; `aA:real`; `S:real`]
      FAWLC_OPPOSITE_V_IMPOSSIBLE) THEN
    FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  FAWOA_STEP(SPECL [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aA:real`;
                    `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_FOUR_AXES) THEN
  MAP_EVERY (fun (sq,f) -> FAWOA_STEP(SPECL sq f) THEN FIRST_X_ASSUM STRIP_ASSUME_TAC)
   [[`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`], ABT_OWNU;
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`], ABT_OWNV;
    [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aA:real`], ABT_OWNU;
    [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aA:real`], ABT_OWNV] THEN
  MAP_EVERY (fun (sq,pt,dir) ->
     let x,y = pt and nx,ny = dir in
     FAWOA_STEP(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)))
   (let qa = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    and qd = [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aA:real`] in
    let m = (`&47 / &20`,`&47 / &20`) and mk = (`&33 / &20`,`&33 / &20`)
    and ce = (`&2`,`&2`) in
    let d1 = (`cD:real`,`--S:real`) and d2 = (`-- --S:real`,`cD:real`)
    and d3 = (`cA:real`,`sA:real`) and d4 = (`--sA:real`,`cA:real`) in
    [qd,mk,d1; qa,m,d1; qd,mk,d2; qa,m,d2; qd,mk,d3; qa,m,d3; qd,mk,d4; qa,m,d4;
     qd,ce,d4]) THEN
  FAWOA_STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sA:real`] [`cA <= &1`] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;

(* Lean: cut *)
let FAWOA_CUT = prove
 (`forall cA sA uA vA aA cD sD uD vD aD S.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aA /\ aA = aD /\
     &0 < cA /\ &0 < sA /\ &4 * sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     sD = --S /\ &0 < cD /\ &0 <= S /\ S <= cD /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&2) (&2) /\
     ldisj cA sA uA vA aA cD sD uD vD aD
     ==> (cA * cD - sA * S) * (uD + aD - &2 * (cD - S)) +
         (cA * S + sA * cD) * (vD + aD - &2 * (cD + S)) < (&13 / &50) * sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWOA_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                    `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `S:real`] FAWOA_SEPARATION) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sD = --S` o concl)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&2) (&113 / &50)`] THEN
  NLIN_FACTS_TAC [] [`&0 <= cA * cD - sA * S`; `&0 <= cA * S + sA * cD`] THEN
  SUBGOAL_THEN `ABT_upper cD (--S) uD vD aD cA sA =
                (cA * cD - sA * S) * (uD + aD) + (cA * S + sA * cD) * (vD + aD)` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cA * cD + sA * --S) = cA * cD - sA * S /\
                  abs(--cA * --S + sA * cD) = cA * S + sA * cD`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(cA * cD - sA * S) * (uD + aD - &2 * (cD - S)) +
                (cA * S + sA * cD) * (vD + aD - &2 * (cD + S)) =
                ((cA * cD - sA * S) * (uD + aD) + (cA * S + sA * cD) * (vD + aD)) -
                &2 * (cA + sA)` SUBST1_TAC THENL
   [UNDISCH_TAC `cD * cD + --S * --S = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_upper cD (--S) uD vD aD cA sA =
                (cA * cD - sA * S) * (uD + aD) + (cA * S + sA * cD) * (vD + aD)`]) THEN
  RASM_ARITH_TAC);;
