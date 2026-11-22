(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeBottomAxes.lean                   *)
(* (namespace N12Compact.CentralNegativeBottomAxes).                         *)
(* The bottom-wall / negative-central pair has only two upward transverse    *)
(* separators.  Squares D, B are 5-tuples (B.s = -t); Lean upper/lower are   *)
(* ABT_upper/ABT_lower, strict_bounds/ownU/ownV/separated/radii are ABT_*,   *)
(* faceSeparation_of_disjoint is CSAT_FACESEPARATION_OF_DISJOINT.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CentralNegativeNeighborBounds.ml";;
needs "n12/geometry/CentralNegativeNeighbor.ml";;

let CNBA_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* the four separating-axis alternatives of two disjoint congruent squares *)
let CNBA_AXES = prove
 (`forall cB sB uB vB a cW sW uW vW.
     cB * cB + sB * sB = &1 /\ cW * cW + sW * sW = &1 /\ &0 < a /\
     ldisj cB sB uB vB a cW sW uW vW a
     ==> (ABT_upper cB sB uB vB a cB sB <= ABT_lower cW sW uW vW a cB sB \/
          ABT_upper cW sW uW vW a cB sB <= ABT_lower cB sB uB vB a cB sB) \/
         (ABT_upper cB sB uB vB a (--sB) cB <= ABT_lower cW sW uW vW a (--sB) cB \/
          ABT_upper cW sW uW vW a (--sB) cB <= ABT_lower cB sB uB vB a (--sB) cB) \/
         (ABT_upper cB sB uB vB a cW sW <= ABT_lower cW sW uW vW a cW sW \/
          ABT_upper cW sW uW vW a cW sW <= ABT_lower cB sB uB vB a cW sW) \/
         (ABT_upper cB sB uB vB a (--sW) cW <= ABT_lower cW sW uW vW a (--sW) cW \/
          ABT_upper cW sW uW vW a (--sW) cW <= ABT_lower cB sB uB vB a (--sW) cW)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `a:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ASM_REWRITE_TAC[C977CB_faceSep] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [DISJ1_TAC; DISJ2_TAC THEN DISJ1_TAC; DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC] THEN
  MATCH_MP_TAC ABT_SEPARATED THENL
   [ALL_TAC; ALL_TAC; GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM];
    GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM]] THEN
  ASM_SIMP_TAC[ABT_PARALLEL_RADIUS; ABT_TRANSVERSE_RADIUS]);;

(* Lean: virtual_point (private) *)
let CNBA_VIRTUAL_POINT = prove
 (`forall c t. c977cc_normal c t
         ==> &3 + c * t - c - t <= &13 / &5 /\ &1 <= &2 - t pow 2 + t - c /\
             (&3 + c * t - c - t) + (&2 - t pow 2 + t - c) <= &18 / &5`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CNNB_OWN_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (&10 / &7 - (c + t))`; `&0 <= (&1 - c) * (&1 - c)`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: positive_lower (private) *)
let CNBA_POSITIVE_LOWER = prove
 (`forall cB sB uB vB aB t d r.
     sB = --t /\ c977cc_normal cB t /\ c977cc_normal d r /\ &1 <= aB /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t
     ==> ABT_lower cB sB uB vB aB d r <= (&13 / &5) * d + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `t:real`] CNBA_VIRTUAL_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= cB * (d - r)`; `&0 <= r * (cB - t)`; `&0 <= d * cB - r * t`;
                     `&0 <= d * t + r * cB`] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                `d:real`; `r:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (d * cB - r * t) * ((&3 * cB - t) - (uB + aB))`;
    `&0 <= (d * t + r * cB) * ((&2 * cB + &3 * t) - (vB + aB))`;
    `&0 <= ((d * cB - r * t) + (d * t + r * cB)) * (aB - &1)`;
    `&0 <= d * (&18 / &5 - ((&3 + cB * t - cB - t) + (&2 - t pow 2 + t - cB)))`;
    `&0 <= (d - r) * ((&2 - t pow 2 + t - cB) - &1)`] THEN
  NLIN_TAC ~deg2:false [CNBA_EQ_HINT `&3 * d + &2 * r` (ASSUME `cB pow 2 + t pow 2 = &1`)]);;

(* Lean: negative_lower (private) *)
let CNBA_NEGATIVE_LOWER = prove
 (`forall cB sB uB vB aB t d r.
     sB = --t /\ c977cc_normal cB t /\ c977cc_normal d r /\ &1 <= aB /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t
     ==> ABT_lower cB sB uB vB aB d (--r) <= (&13 / &5) * d - r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `t:real`] CNBA_VIRTUAL_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= d * cB + r * t`] THEN
  ASM_CASES_TAC `&0 <= d * t - r * cB` THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                  `d:real`; `--r`] C977NCO_LOWER_NEGATIVE_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (d * cB + r * t) * ((&3 * cB - t) - (uB + aB))`;
      `&0 <= (d * t - r * cB) * ((&2 * cB + &3 * t) - (vB + aB))`;
      `&0 <= ((d * cB + r * t) + (d * t - r * cB)) * (aB - &1)`;
      `&0 <= d * (&13 / &5 - (&3 + cB * t - cB - t))`;
      `&0 <= r * ((&2 - t pow 2 + t - cB) - &1)`] THEN
    NLIN_TAC ~deg2:false [CNBA_EQ_HINT `&3 * d - &2 * r` (ASSUME `cB pow 2 + t pow 2 = &1`)];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `d:real`; `--r`]
      C977NCO_LOWER_IN_BANDS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(d * cB + --r * --t) = d * cB + r * t /\
                  abs(--d * --t + --r * cB) = --(d * t - r * cB)` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `linside cB sB uB vB aB (&47 / &20) (&33 / &20)` THEN
    ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN STRIP_TAC THEN
    NLIN_FACTS_TAC [SQ_NONNEG `cB - t`]
     [`&0 <= (d * cB + r * t) * ((&3 * cB - t) - (uB + aB))`;
      `&0 <= --(d * t - r * cB) * ((vB + aB) - (t * &47 / &20 + cB * &33 / &20))`;
      `&0 <= (d * cB + r * t) * (aB - &1)`;
      `&0 <= (&1 - cB) * ((&13 / &20) * cB - &7 / &20)`;
      `cB * t <= &1 / &2`;
      `&2 / &5 - cB - (&13 / &20) * t pow 2 + (&13 / &20) * cB * t <= &0`;
      `&0 <= cB * (cB - t)`;
      `--(&13 / &20) + (&13 / &20) * t pow 2 + (&13 / &20) * cB * t - t <= &0`;
      `&0 <= d * --(&2 / &5 - cB - (&13 / &20) * t pow 2 + (&13 / &20) * cB * t)`;
      `&0 <= r * --(--(&13 / &20) + (&13 / &20) * t pow 2 + (&13 / &20) * cB * t - t)`] THEN
    NLIN_TAC ~deg2:false
      [CNBA_EQ_HINT `&3 * d - (&33 / &20) * r` (ASSUME `cB pow 2 + t pow 2 = &1`)]]);;

let CNBA_SB_TAC (c,s,u,v,a) (x,y) (nx,ny) =
  MP_TAC(SPECL [c; s; u; v; a; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* Lean: alternatives *)
let CNBA_ALTERNATIVES = prove
 (`forall cD sD uD vD aD cB sB uB vB aB t.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sB = --t /\ c977cc_normal cB t /\ &0 < cD /\ abs sD <= cD /\
     aD = aB /\ &1 < aB /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&13 / &5) (&1) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> ABT_upper cD sD uD vD aD t cB <= vB \/
         vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  SUBGOAL_THEN `--cD <= sD /\ sD <= cD` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aD cD sD <= (&13 / &5) * cD + sD` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= sD` THENL
     [MATCH_MP_TAC CNBA_POSITIVE_LOWER THEN EXISTS_TAC `t:real` THEN
      ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aD:real`; `t:real`;
                    `cD:real`; `--sD`] CNBA_NEGATIVE_LOWER) THEN
      ASM_REWRITE_TAC[c977cc_normal; REAL_NEG_NEG] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `cD pow 2 + sD pow 2 = &1 /\ (--sD) pow 2 + cD pow 2 = &1 /\
                cB pow 2 + (--t) pow 2 = &1 /\ t pow 2 + cB pow 2 = &1`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`cD * cD + sD * sD = &1`; `cB * cB + --t * --t = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `--t`; `uB:real`; `vB:real`] CNBA_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aD:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aD:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
  let D = (`cD:real`,`sD:real`,`uD:real`,`vD:real`,`aD:real`)
  and B = (`cB:real`,`--t`,`uB:real`,`vB:real`,`aD:real`)
  and pDm = (`&2`,`&457 / &500`) and pDh = (`&13 / &5`,`&1`)
  and pBm = (`&47 / &20`,`&33 / &20`) and pBw = (`&3`,`&87 / &50`)
  and d1 = (`cD:real`,`sD:real`) and d2 = (`--sD`,`cD:real`)
  and d3 = (`cB:real`,`--t`) and d4 = (`t:real`,`cB:real`) in
  MAP_EVERY (fun (sq,p,d) -> CNBA_SB_TAC sq p d)
   [D,pDh,d1; B,pBw,d1; D,pDm,d1;
    B,pBm,d2; D,pDh,d2;
    D,pDh,d3; B,pBw,d3; D,pDm,d3;
    B,pBm,d4; D,pDm,d4] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o
    check (fun th -> is_disj(concl th) && length(disjuncts(concl th)) = 8)) THENL
   [NLIN_TAC ~deg2:false []; NLIN_TAC ~deg2:false [];
    DISJ2_TAC THEN ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false [];
    NLIN_TAC ~deg2:false []; NLIN_TAC ~deg2:false [];
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]);;
