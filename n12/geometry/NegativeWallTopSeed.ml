(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeWallTopSeed.lean (Jatloe, N12-jatloe).    *)
(* Conditional upper and lower faces of a negative left-wall square.         *)
(* Lean variables C S of the scalar margins are named cc ss here.            *)
(* k = cA*cW - sA*t and h = sA*cW + cA*t are written out.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralLeftWallSeparation.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let NWTS_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: sine_bound (private) *)
let NWTS_SINE_BOUND = prove
 (`forall c s. c977cc_normal c s ==> s <= &71 / &100`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `s * s <= &1 / &2` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (c - s) * (c + s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: longitudinal_margin *)
let NWTS_LONGITUDINAL_MARGIN = prove
 (`forall cc ss d t. c977cc_normal cc ss /\ c977cc_normal d t
     ==> &0 < &1 - d * (&1 - cc) pow 2 / &2 - t * (&22 / &25 + ss * (&1 - cc / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cc:real`; `ss:real`] NWTS_SINE_BOUND) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] NWTS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN
   `&0 <= (cc - &7 / &10) * (&13 / &10 - cc) /\
    &0 <= (&1 - d) * (&1 - cc) pow 2 /\
    &0 <= ss * (cc / &2 - &7 / &20)` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ss * (&1 - cc / &2) <= &923 / &2000` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * (&923 / &2000 - ss * (&1 - cc / &2))` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: transverse_margin *)
let NWTS_TRANSVERSE_MARGIN = prove
 (`forall cc ss d t. c977cc_normal cc ss /\ c977cc_normal d t
     ==> cc * t * ((&22 / &25) * t - (&43 / &500) * d - &1) +
         ss * (&1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * d * t - d) <= &0`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= d * t /\ &0 <= (d - t) * (d + t) /\
                &0 <= (d + t - &1) * (&3 / &2 - (d + t))` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * ((&22 / &25) * t - (&43 / &500) * d - &1) <= &0` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * ((&22 / &25) * t - (&43 / &500) * d - &1) +
                (&1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * d * t - d) < &0`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= &1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * d * t - d` THENL
  [SUBGOAL_THEN
    `&0 <= (cc - ss) * (&1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * d * t - d) /\
     cc * (t * ((&22 / &25) * t - (&43 / &500) * d - &1) +
           (&1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * d * t - d)) < &0`
   MP_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 < a * --b ==> a * b < &0`) THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   REAL_ARITH_TAC;
   SUBGOAL_THEN
    `&0 <= ss * --(&1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * d * t - d) /\
     &0 <= cc * --(t * ((&22 / &25) * t - (&43 / &500) * d - &1))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC]);;

(* one separating-axis case of `alternatives` *)
let NWTS_CASE_TAC nx ny swap radius points =
  let sep = SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                   `cW:real`; `--t:real`; `uW:real`; `vW:real`; `aA:real`; nx; ny]
                  ABT_SEPARATED in
  let sb (sq,(x,y)) =
    let c,s,u,v = sq in
    MP_TAC(SPECL [c; s; u; v; `aA:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
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

(* Lean: alternatives *)
let NWTS_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aA = aW /\ &1 < aA /\ uA + aA <= &2 * (cA + sA) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&12 / &5) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> vA + aA <= ABT_lower cW sW uW vW aW (--sA) cA \/
         uW + aW <= ABT_lower cA sA uA vA aA cW sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW:real = --t`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cA sA`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cW t`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `--t:real`; `uW:real`; `vW:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `--t:real`; `uW:real`; `vW:real`; `aA:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `--t:real`; `uW:real`; `vW:real`; `aA:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let qA = (`cA:real`,`sA:real`,`uA:real`,`vA:real`)
  and qW = (`cW:real`,`--t:real`,`uW:real`,`vW:real`) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [NWTS_CASE_TAC `cA:real` `sA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cW:real`; `--t:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     [qA,(`&3 / &2`,`&2`); qW,(`&457 / &500`,`&2`); qW,(`&1`,`&12 / &5`)];
   NWTS_CASE_TAC `--sA:real` `cA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cW:real`; `--t:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     [qA,(`&2`,`&3 / &2`); qW,(`&1`,`&12 / &5`)];
   NWTS_CASE_TAC `cW:real` `--t:real` true
     (SPECL [`cW:real`; `--t:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     [qA,(`&2`,`&3 / &2`); qW,(`&457 / &500`,`&2`)];
   NWTS_CASE_TAC `-- --t:real` `cW:real` true
     (SPECL [`cW:real`; `--t:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     [qA,(`&3 / &2`,`&2`); qA,(`&33 / &20`,`&33 / &20`);
      qW,(`&457 / &500`,`&2`); qW,(`&1`,`&12 / &5`)]]);;

(* common set-up of upper_face / lower_face: after substitution sW = --t and *)
(* aW = aA, adds k >= 0, h >= 0, both lower-support formulas and the        *)
(* alternatives of NWTS_ALTERNATIVES                                         *)
let NWTS_FACE_SETUP_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW:real = --t`)) THEN
  C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `--t:real`; `uW:real`; `vW:real`; `aA:real`; `t:real`]
    NWTS_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= cA * cW - sA * t /\ &0 <= sA * cW + cA * t` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= cW * (cA - sA) /\ &0 <= sA * (cW - t) /\
                 &0 <= sA * cW /\ &0 <= cA * t` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--t:real`; `uW:real`; `vW:real`; `aA:real`; `t:real`;
                `--sA:real`; `cA:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `ABT_lower cA sA uA vA aA cW (--t) =
                (cA * cW - sA * t) * uA - (sA * cW + cA * t) * (vA + aA)`
  ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   SUBGOAL_THEN `abs(cW * cA + --t * sA) = cA * cW - sA * t /\
                 abs(--cW * sA + --t * cA) = sA * cW + cA * t`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  NWTS_UNFOLD_TAC `linside cA sA uA vA aA (&3 / &2) (&2)` THEN
  NWTS_UNFOLD_TAC `linside cW (--t) uW vW aA (&457 / &500) (&2)`;;

(* Lean: upper_face *)
let NWTS_UPPER_FACE = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aA = aW /\ &1 < aA /\ uA + aA <= &2 * (cA + sA) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     linside cW sW uW vW aW (&1) (&12 / &5) /\
     ~linside cW sW uW vW aW (&1) (&72 / &25) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> vW + aW <= t + (&72 / &25) * cW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NWTS_FACE_SETUP_TAC THEN
  NWTS_UNFOLD_TAC `linside cW (--t) uW vW aA (&1) (&113 / &50)` THEN
  SUBGOAL_THEN `uW < cW - (&72 / &25) * t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `t:real`] NWTS_TRANSVERSE_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= (sA * cW + cA * t) * ((uW + aA) - (cW - (&72 / &25) * t + &1)) /\
      &0 <= (cA * cW - sA * t) * (((&457 / &500) * t + &2 * cW) - vW)` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `--(sA * cW + cA * t) * (cW - (&72 / &25) * t + &1) +
      (cA * cW - sA * t) * ((&457 / &500) * t + &2 * cW) - (&2 * cA - (&3 / &2) * sA) =
      cA * t * ((&22 / &25) * t - (&43 / &500) * cW - &1) +
      sA * (&1 / &2 + (&43 / &500) * t pow 2 + (&22 / &25) * cW * t - cW)` MP_TAC THENL
    [UNDISCH_TAC `c977cc_normal cW t` THEN REWRITE_TAC[c977cc_normal] THEN
     STRIP_TAC THEN UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
     ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `t:real`] NWTS_LONGITUDINAL_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= (cA * cW - sA * t) * (&2 * (cA + sA) - &1 - uA) /\
      &0 <= (sA * cW + cA * t) * ((vA + aA) - (&2 * cA - (&3 / &2) * sA))` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `cW - (&72 / &25) * t + &1 -
      ((cA * cW - sA * t) * (&2 * (cA + sA) - &1) -
       (sA * cW + cA * t) * (&2 * cA - (&3 / &2) * sA)) =
      &1 - cW * (&1 - cA) pow 2 / &2 - t * (&22 / &25 + sA * (&1 - cA / &2))` MP_TAC THENL
    [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cW (--t) uW vW aA (&1) (&72 / &25)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: lower_face *)
let NWTS_LOWER_FACE = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aA = aW /\ &1 < aA /\ uA + aA <= &2 * (cA + sA) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&12 / &5) /\
     ~linside cW sW uW vW aW (&19 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> (&19 / &25) * t + (&187 / &100) * cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NWTS_FACE_SETUP_TAC THEN
  SUBGOAL_THEN `uW < (&19 / &25) * cW - (&187 / &100) * t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `&37 / &50 - (&77 / &500) * t pow 2 - (&13 / &100) * cW * t - cW <= &0`
    ASSUME_TAC THENL
    [SUBGOAL_THEN `&0 <= cW * (&1 - cW) /\ &0 <= cW * t` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     UNDISCH_TAC `c977cc_normal cW t` THEN REWRITE_TAC[c977cc_normal] THEN
     REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN NLIN_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (sA * cW + cA * t) * ((uW + aA) - ((&19 / &25) * cW - (&187 / &100) * t + &1)) /\
      &0 <= (cA * cW - sA * t) * (((&457 / &500) * t + &2 * cW) - vW) /\
      &0 <= (cA * t) * --((&77 / &500) * cW - (&13 / &100) * t - &1) /\
      &0 <= sA * --(&37 / &50 - (&77 / &500) * t pow 2 - (&13 / &100) * cW * t - cW)`
    MP_TAC THENL
    [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `--(sA * cW + cA * t) * ((&19 / &25) * cW - (&187 / &100) * t + &1) +
      (cA * cW - sA * t) * ((&457 / &500) * t + &2 * cW) - (&2 * cA - (&3 / &2) * sA) =
      cA * t * ((&77 / &500) * cW - (&13 / &100) * t - &1) +
      sA * (&37 / &50 - (&77 / &500) * t pow 2 - (&13 / &100) * cW * t - cW)` MP_TAC THENL
    [UNDISCH_TAC `c977cc_normal cW t` THEN REWRITE_TAC[c977cc_normal] THEN
     STRIP_TAC THEN UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
     ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`] NWTS_SINE_BOUND) THEN
    MP_TAC(SPECL [`cW:real`; `t:real`] NWTS_SINE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= (cA - &7 / &10) * (&13 / &10 - cA) /\
      &0 <= (&1 - cW) * (&1 - cA) pow 2 /\
      &0 <= sA * (cA / &2 - &7 / &20)` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
     REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t * (&923 / &2000 - sA * (&1 - cA / &2))` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (cA * cW - sA * t) * (&2 * (cA + sA) - &1 - uA) /\
      &0 <= (sA * cW + cA * t) * ((vA + aA) - (&2 * cA - (&3 / &2) * sA))` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&19 / &25) * cW - (&187 / &100) * t + &1 -
      ((cA * cW - sA * t) * (&2 * (cA + sA) - &1) -
       (sA * cW + cA * t) * (&2 * cA - (&3 / &2) * sA)) =
      &1 - (&6 / &25) * cW - cW * (&1 - cA) pow 2 / &2 +
      t * (&13 / &100 - sA * (&1 - cA / &2))` MP_TAC THENL
    [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cW (--t) uW vW aA (&19 / &25) (&187 / &100)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: tilt *)
let NWTS_TILT = prove
 (`forall d t a lo hi. c977cc_normal d t /\ &1 < a /\ hi = lo + a /\
                 (&19 / &25) * t + (&187 / &100) * d <= lo /\
                 hi <= t + (&72 / &25) * d
                 ==> t < &51 / &100`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(&4 / &5) * d + (&3 / &5) * t <= &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `((&4 / &5) * d + (&3 / &5) * t) * ((&4 / &5) * d + (&3 / &5) * t) <= &1`
   MP_TAC THENL
   [MP_TAC(SPEC `&3 * d - &4 * t` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(`(&4 / &5) * d + (&3 / &5) * t`,`w:real`) THEN GEN_TAC THEN DISCH_TAC THEN
   NLIN_TAC [SQ_NONNEG `w - &1`]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
