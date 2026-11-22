(* ========================================================================= *)
(* Port of Compact/Geometry/DiagonalOuterElbow.lean                          *)
(*                                                                           *)
(* Normal c t is c977cc_normal; lower/upper are ABT_lower/ABT_upper.  The    *)
(* private helpers take the wall R = (cR, sR, uR, vR, aR) with sR = --t.     *)
(* The four-axis case split (faceSeparation_of_disjoint + separated) is      *)
(* ABT_FOUR_AXES.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/DiagonalWallCenter.ml";;
needs "n12/geometry/DiagonalOuterElbowBounds.ml";;

(* apply a lemma instance: prove its antecedent from the assumptions, then
   add its conclusion as an assumption *)
let DOE_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj; c977cc_normal]) THEN
     REWRITE_TAC[lcont; ldisj; c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

(* unfold a positive membership assumption into its four strict inequalities *)
let DOE_UNFOLD_TAC t = STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t));;

(* Lean: corner (private) *)
let DOE_CORNER = prove
 (`forall c s u v a p r. c * c + s * s = &1 /\ u <= p /\ p <= u + a /\ v <= r /\ r <= v + a
     ==> lclosed c s u v a (c * p - s * r) (s * p + c * r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * p - s * r) + s * (s * p + c * r) = p /\
                --s * (c * p - s * r) + c * (s * p + c * r) = r`
    (fun th -> REWRITE_TAC[th] THEN ASM_REAL_ARITH_TAC) THEN
  CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* Lean: alternatives (private) *)
let DOE_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &0 < cA /\ &0 <= sA /\ c977cc_normal cR t /\
     sR = --t /\ &2 * t <= cR /\ aA = aR /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cR sR uR vR aR (--sA) cA <= vA \/
         ABT_upper cA sA uA vA aA cR (--t) <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sR = --t` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  DOE_STEP(SPECL [`cR:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`] ABT_FOUR_AXES) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MAP_EVERY (fun (sq,pt,dir) ->
     let x,y = pt and nx,ny = dir in
     DOE_STEP(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)))
   (let qa = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    and qr = [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`] in
    let p = (`&2`,`&113 / &50`) and f = (`&113 / &50`,`&3`)
    and mk = (`&1543 / &500`,`&2`) and tp = (`&12 / &5`,`&3`) in
    let d1 = (`cA:real`,`sA:real`) and d2 = (`--sA:real`,`cA:real`)
    and d3 = (`cR:real`,`--t:real`) and d4 = (`-- --t:real`,`cR:real`) in
    [qa,p,d1; qr,tp,d1; qa,f,d2; qr,mk,d2; qa,p,d3; qr,mk,d3;
     qa,f,d4; qr,mk,d4; qa,p,d4; qr,tp,d4]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;

(* Lean: shallow (private) *)
let DOE_SHALLOW = prove
 (`forall cA sA uA vA aA cR sR uR vR aR t.
     cA * cA + sA * sA = &1 /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ c977cc_normal cA sA /\ c977cc_normal cR t /\
     sR = --t /\ &2 * t <= cR /\ aA = aR /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&2) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sR = --t` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  DOE_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  DOE_STEP(SPECL [`cR:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`; `t:real`] DOE_ALTERNATIVES) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY DOE_UNFOLD_TAC
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cA sA uA vA aA (&113 / &50) (&3)`;
    `linside cA sA uA vA aA (&47 / &20) (&47 / &20)`;
    `linside cR (--t) uR vR aA (&1543 / &500) (&2)`; `linside cR (--t) uR vR aA (&12 / &5) (&3)`] THEN
  SUBGOAL_THEN `&2 * cA + &2 * sA <= uA \/ &2 * cA - &2 * sA <= vA` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside cA sA uA vA aA (&2) (&2)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * cA - &2 * sA <= vA ==> (&33 / &20) * cA + (&47 / &20) * sA <= uA`
    ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside cA sA uA vA aA (&33 / &20) (&47 / &20)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cR * cA - t * sA`; `&0 <= cR * sA + t * cA`;
    `uR < (&12 / &5) * cR - &3 * t`; `vR < (&1543 / &500) * t + &2 * cR`] THEN
  (* the support of A in the direction (cR,--t), from its corner (uA + aA, vA) *)
  DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `uA + aA:real`; `vA:real`]
    DOE_CORNER) THEN
  DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
     `cA * (uA + aA) - sA * vA`; `sA * (uA + aA) + cA * vA`; `cR:real`; `--t:real`] ABT_CLOSED_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cR * (cA * (uA + aA) - sA * vA) + --t * (sA * (uA + aA) + cA * vA) =
                (cR * cA - t * sA) * (uA + aA) - (cR * sA + t * cA) * vA` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`(cR * sA + t * cA) * vA <= (cR * sA + t * cA) * ((&47 / &20) * (cA - sA))`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
    check (fun th -> can (find_term ((=) `ABT_lower`)) (concl th))) THENL
   [(* A below R along A's normal *)
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `&2 * cA + &2 * sA`)) (concl th))) THENL
     [DOE_STEP(SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`; `uR:real`; `vR:real`]
        DOE_CORNER) THEN
      DOE_STEP(SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`;
         `cR * uR - --t * vR`; `--t * uR + cR * vR`; `cA:real`; `sA:real`] ABT_CLOSED_BOUNDS) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(cR * cA - t * sA) * ((&12 / &5) * cR - &3 * t) +
                    (cR * sA + t * cA) * ((&1543 / &500) * t + &2 * cR) =
                    &2 * (cA + sA) + cA * (&2 / &5 + (&343 / &500) * t pow 2 - cR * t) +
                    sA * (t pow 2 + (&343 / &500) * cR * t)` ASSUME_TAC THENL
       [UNDISCH_TAC `cR pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      DOE_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `t:real`] DOEB_SHALLOW_INCOMING) THEN
      NLIN_FACTS_TAC []
       [`(cR * cA - t * sA) * uR <= (cR * cA - t * sA) * ((&12 / &5) * cR - &3 * t)`;
        `(cR * sA + t * cA) * vR <= (cR * sA + t * cA) * ((&1543 / &500) * t + &2 * cR)`] THEN
      RASM_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) then
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP th) else NO_TAC) THEN
      DOE_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`;
         `&12 / &5`; `&3`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS)) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
      NLIN_FACTS_TAC [SQ_NONNEG `(&13 / &20) * cA - (&3 / &4) * sA`]
       [`(&3 / &4) * cA + (&13 / &20) * sA < &1`] THEN
      RASM_ARITH_TAC];
    (* R below A along A's transverse direction *)
    DOE_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`;
       `&12 / &5`; `&3`; `--sA:real`; `cA:real`] ABT_STRICT_BOUNDS)) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN RASM_ARITH_TAC;
    (* A below R along R's normal *)
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `&2 * cA + &2 * sA`)) (concl th))) THENL
     [SUBGOAL_THEN `(cR * cA - t * sA) * (&2 * cA + &2 * sA + &1) -
                    (cR * sA + t * cA) * ((&47 / &20) * (cA - sA)) - ((&12 / &5) * cR - &3 * t) =
                    cR * (cA - &2 / &5 + (&7 / &20) * sA pow 2 - (&7 / &20) * cA * sA) +
                    t * (&13 / &20 - sA + (&7 / &20) * sA pow 2 + (&7 / &20) * cA * sA)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      DOE_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `t:real`] DOEB_SHALLOW_U) THEN
      NLIN_FACTS_TAC []
       [`(cR * cA - t * sA) * (&2 * cA + &2 * sA + &1) <= (cR * cA - t * sA) * (uA + aA)`] THEN
      RASM_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) then
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP th) else NO_TAC) THEN
      SUBGOAL_THEN `(cR * cA - t * sA) * ((&33 / &20) * cA + (&47 / &20) * sA + &1) -
                    (cR * sA + t * cA) * ((&47 / &20) * (cA - sA)) - ((&12 / &5) * cR - &3 * t) =
                    cR * (cA - &3 / &4 + (&7 / &10) * sA pow 2) +
                    t * (&13 / &20 - sA + (&7 / &10) * cA * sA)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      DOE_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `t:real`] DOEB_SHALLOW_V) THEN
      NLIN_FACTS_TAC []
       [`(cR * cA - t * sA) * ((&33 / &20) * cA + (&47 / &20) * sA + &1) <=
         (cR * cA - t * sA) * (uA + aA)`] THEN
      RASM_ARITH_TAC]]);;

(* Lean: steep (private) *)
let DOE_STEEP = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT t.
     cA * cA + sA * sA = &1 /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ &0 < cA /\ c977cc_normal sA cA /\ c977cc_normal cR t /\
     sR = --t /\ &2 * t <= cR /\ aA = aR /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&2) (&2) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     linside cT sT uT vT aT (&87 / &50) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sR = --t` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  DOE_STEP(SPECL [`sA:real`; `cA:real`] C977CC_NORMAL_BOUNDS) THEN
  DOE_STEP(SPECL [`cR:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`; `t:real`] DOE_ALTERNATIVES) THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&87 / &50) (&3)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aT` THEN REWRITE_TAC[ldisj] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY DOE_UNFOLD_TAC
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cA sA uA vA aA (&113 / &50) (&3)`;
    `linside cA sA uA vA aA (&47 / &20) (&47 / &20)`;
    `linside cR (--t) uR vR aA (&1543 / &500) (&2)`; `linside cR (--t) uR vR aA (&12 / &5) (&3)`] THEN
  SUBGOAL_THEN `&2 * cA + &2 * sA <= uA` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside cA sA uA vA aA (&2) (&2)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vA + aA <= &3 * cA - (&87 / &50) * sA` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside cA sA uA vA aA (&87 / &50) (&3)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
    check (fun th -> can (find_term ((=) `ABT_lower`)) (concl th))) THENL
   [DOE_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
       `&113 / &50`; `&3`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS)) THEN
    DOE_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`;
       `&1543 / &500`; `&2`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS)) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
      then STRIP_ASSUME_TAC th else NO_TAC)) THEN
    RASM_ARITH_TAC;
    DOE_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`;
       `&12 / &5`; `&3`; `--sA:real`; `cA:real`] ABT_STRICT_BOUNDS)) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN RASM_ARITH_TAC;
    DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
       `(&113 / &50) * cA + &3 * sA`; `vA:real`] DOE_CORNER) THEN
    DOE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
       `cA * ((&113 / &50) * cA + &3 * sA) - sA * vA`;
       `sA * ((&113 / &50) * cA + &3 * sA) + cA * vA`; `cR:real`; `--t:real`] ABT_CLOSED_BOUNDS) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(cR * cA - t * sA) * ((&113 / &50) * cA + &3 * sA) -
                  (cR * sA + t * cA) * (&3 * cA - (&87 / &50) * sA - &1) -
                  ((&12 / &5) * cR - &3 * t) =
                  cR * (sA - (&13 / &25) * sA pow 2 - &7 / &50) +
                  t * cA * (&1 - (&13 / &25) * sA)` ASSUME_TAC THENL
     [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    DOE_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `t:real`] DOEB_STEEP) THEN
    NLIN_FACTS_TAC []
     [`&0 <= cR * sA + t * cA`; `vA <= &3 * cA - (&87 / &50) * sA - &1`;
      `(cR * sA + t * cA) * vA <= (cR * sA + t * cA) * (&3 * cA - (&87 / &50) * sA - &1)`;
      `uR < (&12 / &5) * cR - &3 * t`] THEN
    RASM_ARITH_TAC]);;

(* Lean: point *)
let DOE_POINT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ aR <= &1001 / &1000 /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ~linside cR sR uR vR aR (&3) (&3) /\
     linside cT sT uT vT aT (&87 / &50) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aa:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aa:real = aA` o concl)) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = aA` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  DOE_STEP(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `aA:real`] DWC_WALL_FRAME) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  ASM_CASES_TAC `linside ca sa ua va aA (&2) (&2)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `sa <= ca` THENL
   [DOE_STEP(SPECL [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aA:real`;
                    `cr:real`; `sr:real`; `ur:real`; `vr:real`; `aA:real`; `--sr:real`] DOE_SHALLOW);
    DOE_STEP(SPECL [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aA:real`;
                    `cr:real`; `sr:real`; `ur:real`; `vr:real`; `aA:real`;
                    `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`; `--sr:real`] DOE_STEEP)] THEN
  FIRST_X_ASSUM CONTR_TAC);;
