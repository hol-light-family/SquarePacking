(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveOpposite.lean                 *)
(*                                                                           *)
(* Narrow elbow A = (cA, sA, uA, vA, aA), opposite square D in a positive    *)
(* canonical frame.  Normal is c977cc_normal; lower/upper are                *)
(* ABT_lower/ABT_upper; the four-axis case split is ABT_FOUR_AXES.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/FullAuxWallLowerCorner.ml";;
needs "n12/geometry/FullAuxWallOppositeAxes.ml";;

let FAWPO_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj; c977cc_normal]) THEN
     REWRITE_TAC[lcont; ldisj; c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

let FAWPO_STRIP_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC));;

let FAWPO_UNFOLD_TAC ts =
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t))) ts;;

(* Lean: bands_closed (private) *)
let FAWPO_BANDS_CLOSED = prove
 (`forall c s u v a p q. c * c + s * s = &1 /\ u <= p /\ p <= u + a /\ v <= q /\ q <= v + a
     ==> lclosed c s u v a (c * p - s * q) (s * p + c * q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * p - s * q) + s * (s * p + c * q) = p /\
                --s * (c * p - s * q) + c * (s * p + c * q) = q`
    (fun th -> REWRITE_TAC[th] THEN ASM_REAL_ARITH_TAC) THEN
  CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* Lean: central_v_band *)
let FAWPO_CENTRAL_V_BAND = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 < s /\ &4 * s <= c /\
     linside c s u v a (&5 / &2) (&3) /\ v + a <= &3 * c - (&12 / &5) * s
     ==> v < &2 * (c - s) /\ &2 * (c - s) < v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWPO_UNFOLD_TAC [`linside c s u v a (&5 / &2) (&3)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN RASM_ARITH_TAC);;

(* Lean: opposite_v_impossible (private) *)
let FAWPO_OPPOSITE_V_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     &1 < aA /\ c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &0 < sA /\ &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\
     vD + aD <= ABT_lower cA sA uA vA aA (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWPO_STEP(SPECL [`cD:real`; `sD:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `uA:real`; `vA:real`]
    FAWPO_BANDS_CLOSED) THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
     `cA * uA - sA * vA`; `sA * uA + cA * vA`; `--sD:real`; `cD:real`] ABT_CLOSED_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWPO_STRIP_TAC THEN
  FAWPO_UNFOLD_TAC [`linside cA sA uA vA aA (&2) (&113 / &50)`;
                    `linside cD sD uD vD aD (&2) (&2)`] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA - &2 * (cA + sA)`; `vA - &2 * (cA - sA)`] FAWLC_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `--sD * (cA * uA - sA * vA) + cD * (sA * uA + cA * vA) - &2 * (cD - sD) =
                --sD * (cA * (uA - &2 * (cA + sA)) - sA * (vA - &2 * (cA - sA))) +
                cD * (sA * (uA - &2 * (cA + sA)) + cA * (vA - &2 * (cA - sA)))` ASSUME_TAC THENL
   [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cA * (uA - &2 * (cA + sA)) - sA * (vA - &2 * (cA - sA))`;
    `--sD * (cA * (uA - &2 * (cA + sA)) - sA * (vA - &2 * (cA - sA))) <= &0`;
    `cD * (sA * (uA - &2 * (cA + sA)) + cA * (vA - &2 * (cA - sA))) < &0`] THEN
  RASM_ARITH_TAC);;

(* Lean: alternatives *)
let FAWPO_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aA /\ aA = aD /\ c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &0 < sA /\ &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&2) (&2) /\
     ldisj cA sA uA vA aA cD sD uD vD aD
     ==> ABT_upper cD sD uD vD aD cA sA <= uA \/
         uD + aD <= ABT_lower cA sA uA vA aA cD sD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aD` o concl)) THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWPO_STEP(SPECL [`cD:real`; `sD:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWPO_STRIP_TAC THEN
  SUBGOAL_THEN `~(vD + aA <= ABT_lower cA sA uA vA aA (--sD) cD)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aA:real`]
      FAWPO_OPPOSITE_V_IMPOSSIBLE) THEN
    FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FAWPO_CENTRAL_V_BAND) THEN
  FAWPO_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aA:real`;
                    `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_FOUR_AXES) THEN
  MAP_EVERY (fun (sq,f) -> FAWPO_STEP(SPECL sq f) THEN FIRST_X_ASSUM STRIP_ASSUME_TAC)
   [[`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`], ABT_OWNU;
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`], ABT_OWNV;
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aA:real`], ABT_OWNU;
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aA:real`], ABT_OWNV] THEN
  MAP_EVERY (fun (sq,pt,dir) ->
     let x,y = pt and nx,ny = dir in
     FAWPO_STEP(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)))
   (let qa = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    and qd = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aA:real`] in
    let m = (`&47 / &20`,`&47 / &20`) and mk = (`&33 / &20`,`&33 / &20`)
    and ce = (`&2`,`&2`) in
    let d1 = (`cD:real`,`sD:real`) and d2 = (`--sD:real`,`cD:real`)
    and d3 = (`cA:real`,`sA:real`) and d4 = (`--sA:real`,`cA:real`) in
    [qd,mk,d1; qa,m,d1; qd,mk,d2; qa,m,d2; qd,mk,d3; qa,m,d3; qd,mk,d4; qa,m,d4;
     qd,ce,d4]) THEN
  FAWPO_STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWPO_STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;

(* Lean: upper_u_offset *)
let FAWPO_UPPER_U_OFFSET = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aA /\ c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &0 < sA /\ &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\
     (ABT_upper cD sD uD vD aD cA sA <= uA \/
      uD + aD <= ABT_lower cA sA uA vA aA cD sD)
     ==> &0 < uD + aD - &2 * (cD + sD) /\ uD + aD - &2 * (cD + sD) < &1 / &10`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWPO_STEP(SPECL [`cD:real`; `sD:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `cD:real`; `sD:real`] C977CSB_DOT_LE_ONE) THEN
  FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FAWPO_CENTRAL_V_BAND) THEN
  FAWPO_STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWPO_STRIP_TAC THEN
  FAWPO_UNFOLD_TAC [`linside cA sA uA vA aA (&2) (&113 / &50)`;
                    `linside cD sD uD vD aD (&2) (&2)`] THEN
  NLIN_FACTS_TAC [] [`&0 < cA * cD + sA * sD`; `(&7 / &10) * cA <= cA * cD + sA * sD`] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
  (CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THENL
   [FAWPO_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
       `uD + aD:real`; `&2 * (cD - sD)`] FAWPO_BANDS_CLOSED) THEN
    FAWPO_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
       `cD * (uD + aD) - sD * (&2 * (cD - sD))`; `sD * (uD + aD) + cD * (&2 * (cD - sD))`;
       `cA:real`; `sA:real`] ABT_CLOSED_BOUNDS) THEN
    FAWPO_STRIP_TAC THEN
    SUBGOAL_THEN `cA * (cD * (uD + aD) - sD * (&2 * (cD - sD))) +
                  sA * (sD * (uD + aD) + cD * (&2 * (cD - sD))) - &2 * (cA + sA) =
                  (cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD))` ASSUME_TAC THENL
     [UNDISCH_TAC `cD * cD + sD * sD = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`(cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD)) < (&13 / &50) * sA`;
      `&0 <= (cA * cD + sA * sD) * ((uD + aD - &2 * (cD + sD)) - &1 / &10)`] THEN
    RASM_ARITH_TAC;
    FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
       `uA:real`; `&2 * (cA - sA)`] FAWPO_BANDS_CLOSED) THEN
    FAWPO_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
       `cA * uA - sA * (&2 * (cA - sA))`; `sA * uA + cA * (&2 * (cA - sA))`;
       `cD:real`; `sD:real`] ABT_CLOSED_BOUNDS) THEN
    FAWPO_STRIP_TAC THEN
    SUBGOAL_THEN `cD * (cA * uA - sA * (&2 * (cA - sA))) +
                  sD * (sA * uA + cA * (&2 * (cA - sA))) - &2 * (cD + sD) =
                  (cA * cD + sA * sD) * (uA - &2 * (cA + sA))` ASSUME_TAC THENL
     [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (uA - &2 * (cA + sA)) * (&1 - (cA * cD + sA * sD))`] THEN
    RASM_ARITH_TAC]);;

(* Lean: lower_v_face *)
let FAWPO_LOWER_V_FACE = prove
 (`forall c s u v a.
     c977cc_normal c s /\ &1 < a /\ linside c s u v a (&2) (&2) /\
     u + a - &2 * (c + s) < &1 / &10 /\
     ~linside c s u v a (&87 / &50) (&1)
     ==> c - (&87 / &50) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWPO_STRIP_TAC THEN
  FAWPO_UNFOLD_TAC [`linside c s u v a (&2) (&2)`] THEN
  MP_TAC(ASSUME `~linside c s u v a (&87 / &50) (&1)`) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;
