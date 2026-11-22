(* ========================================================================= *)
(* Port of Compact/Geometry/C84MergedPair.lean                               *)
(* (namespace N12Compact.C84MergedPair).                                     *)
(* upper/lower/strict_bounds/ownV/separated/parallel_radius/                 *)
(* transverse_radius: ABT_*; faceSeparation_of_disjoint:                     *)
(* CSAT_FACESEPARATION_OF_DISJOINT; canonical_frame: CLF_CANONICAL_FRAME.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C84MergedBottom.ml";;
needs "n12/geometry/C84PairMargins.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* support values of a square in a direction, via its face coordinates *)
let C84MP_SUPPORT = prove
 (`forall c s u v a nx ny. c * c + s * s = &1
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) -
         a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c)) /\
         ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) +
         a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[ABT_lower; ABT_upper; tss_support_radius] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nx * lcx c s u v a + ny * lcy c s u v a =
     (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2)`
    (fun th -> REWRITE_TAC[th]) THEN
  MAP_EVERY UNDISCH_TAC [`c * c + s * s = &1`;
    `c * lcx c s u v a + s * lcy c s u v a = u + a / &2`;
    `--s * lcx c s u v a + c * lcy c s u v a = v + a / &2`] THEN
  CONV_TAC REAL_RING);;

(* the four separating-axis alternatives of two disjoint congruent squares *)
let C84MP_AXES = prove
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

let C84MP_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let C84MP_SB_TAC (c,s,u,v,a) (x,y) (nx,ny) =
  MP_TAC(SPECL [c; s; u; v; a; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* Lean: canonical_impossible (private) *)
let C84MP_CANONICAL_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cW sW uW vW aW.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aB /\ aB = aW /\
     &0 < cB /\ &0 < sB /\ sB <= cB /\ &0 < cW /\ abs sW <= cW /\
     linside cB sB uB vB aB (&2) (&457 / &500) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     linside cW sW uW vW aW (&33 / &20) (&33 / &20) /\
     linside cW sW uW vW aW (&33 / &20) (&47 / &20) /\
     linside cW sW uW vW aW (&87 / &50) (&2) /\
     ~linside cB sB uB vB aB (&33 / &20) (&33 / &20) /\
     ~linside cB sB uB vB aB (&113 / &50) (&1) /\
     ldisj cB sB uB vB aB cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aW`)) THEN
  SUBGOAL_THEN `cB pow 2 + sB pow 2 = &1 /\ (--sB) pow 2 + cB pow 2 = &1 /\
                cW pow 2 + sW pow 2 = &1 /\ (--sW) pow 2 + cW pow 2 = &1`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`cB * cB + sB * sB = &1`; `cW * cW + sW * sW = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `--cW <= sW /\ sW <= cW` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`] C84MP_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let lin ts = MAP_EVERY (fun t -> MP_TAC(ASSUME t)) ts THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC in
  let bot = `linside cB sB uB vB aB (&2) (&457 / &500)`
  and se = `linside cB sB uB vB aB (&47 / &20) (&33 / &20)`
  and rt = `linside cB sB uB vB aB (&113 / &50) (&2)`
  and nsw = `~linside cB sB uB vB aB (&33 / &20) (&33 / &20)`
  and ng5 = `~linside cB sB uB vB aB (&113 / &50) (&1)` in
  SUBGOAL_THEN `uB < cB * &2 + sB * &457 / &500 /\ vB < --sB * &2 + cB * &457 / &500`
    STRIP_ASSUME_TAC THENL [lin [bot]; ALL_TAC] THEN
  SUBGOAL_THEN `cB - (&113 / &50) * sB <= vB` ASSUME_TAC THENL
   [lin [ng5; bot; se; rt]; ALL_TAC] THEN
  SUBGOAL_THEN `(&43 / &500) * cB < (&13 / &50) * sB` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &10 < sB` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC [] [`&0 <= (&3 / &10 - sB) * (&3 / &10 + sB)`; `&19 / &20 <= cB`] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C84PM_PARALLEL) THEN
  SUBGOAL_THEN `(&33 / &20) * (cB + sB) <= uB` ASSUME_TAC THENL
   [lin [nsw; bot; se]; ALL_TAC] THEN
  let B = (`cB:real`,`sB:real`,`uB:real`,`vB:real`,`aB:real`)
  and W = (`cW:real`,`sW:real`,`uW:real`,`vW:real`,`aB:real`)
  and pBot = (`&2`,`&457 / &500`) and pSE = (`&47 / &20`,`&33 / &20`)
  and pSW = (`&33 / &20`,`&33 / &20`) and pNW = (`&33 / &20`,`&47 / &20`)
  and pIn = (`&87 / &50`,`&2`)
  and dBU = (`cB:real`,`sB:real`) and dBV = (`--sB`,`cB:real`)
  and dWU = (`cW:real`,`sW:real`) and dWV = (`--sW`,`cW:real`) in
  MAP_EVERY (fun (sq,p,d) -> C84MP_SB_TAC sq p d)
   [B,pSE,dBU; B,pBot,dBU; W,pSW,dBU; W,pNW,dBU;
    W,pSW,dBV; W,pNW,dBV; B,pSE,dBV;
    B,pSE,dWU; B,pBot,dWU; W,pSW,dWU; W,pNW,dWU; W,pIn,dWU;
    W,pSW,dWV; W,pNW,dWV; B,pBot,dWV] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cB - sB) * cW`; `&0 <= sB * (cW + sW)`; `&0 <= cW * cB + sW * sB`] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o
    check (fun th -> is_disj(concl th) && length(disjuncts(concl th)) = 8)) THENL
   [(* noBU *) NLIN_TAC ~deg2:false [];
    NLIN_TAC ~deg2:false [];
    (* noBV *) NLIN_TAC ~deg2:false [];
    NLIN_TAC ~deg2:false [];
    (* noWU, first *) NLIN_TAC ~deg2:false [];
    (* noWU, second *)
    (ASM_CASES_TAC `&0 <= sW * cB - cW * sB` THENL
     [NLIN_FACTS_TAC []
       [`&0 <= sW`; `cB <= &1`; `&0 <= sW * (&1 - cB)`; `cW * (&3 / &10) <= cW * sB`;
        `(&3 / &10) * cW <= sW`] THEN
      NLIN_TAC ~deg2:false [];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      MP_TAC(CONJUNCT1(UNDISCH(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
        `cW:real`; `sW:real`] C84MP_SUPPORT))) THEN
      SUBGOAL_THEN `abs(cW * cB + sW * sB) = cW * cB + sW * sB /\
                    abs(--cW * sB + sW * cB) = --(--cW * sB + sW * cB)`
        (fun th -> REWRITE_TAC[th]) THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`(cW * cB + sW * sB) * uB <= (cW * cB + sW * sB) * (cB * &2 + sB * &457 / &500)`;
        `&1 + cB - (&113 / &50) * sB <= vB + aB`;
        `(sW * cB - cW * sB) * (vB + aB) <= (sW * cB - cW * sB) * (&1 + cB - (&113 / &50) * sB)`] THEN
      MP_TAC(SPECL [`cB:real`; `sB:real`] C84PM_MARGINS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[C84PM_A_DEF; C84PM_D_DEF] THEN STRIP_TAC THEN
      ASM_CASES_TAC `&0 <= sW` THENL
       [NLIN_FACTS_TAC [] [`cW * (&13 / &50 + (&13 / &50) * sB pow 2 - (&43 / &500) * cB * sB - sB) < &0`; `sW * (-- &1 - (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB + cB) <= &0`] THEN
        NLIN_TAC ~deg2:false [C84MP_EQ_HINT `cW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`);
       C84MP_EQ_HINT `sW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`)];
        ASM_CASES_TAC `&35 * --sW <= &9 * cW` THENL
         [NLIN_FACTS_TAC []
           [`cW * (&35 * (&13 / &50 + (&13 / &50) * sB pow 2 - (&43 / &500) * cB * sB - sB) - &9 * (-- &1 - (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB + cB)) < &0`; `(&9 * cW - &35 * --sW) * (-- &1 - (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB + cB) <= &0`] THEN
          NLIN_TAC ~deg2:false [C84MP_EQ_HINT `cW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`);
       C84MP_EQ_HINT `sW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`)];
          NLIN_FACTS_TAC []
           [`(cW + sW) * (&35 * (&13 / &50 + (&13 / &50) * sB pow 2 - (&43 / &500) * cB * sB - sB) - &9 * (-- &1 - (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB + cB)) <= &0`;
            `(&35 * --sW - &9 * cW) * ((&13 / &50 + (&13 / &50) * sB pow 2 - (&43 / &500) * cB * sB - sB) - (-- &1 - (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB + cB) - &13 / &50) < &0`] THEN
          NLIN_TAC ~deg2:false [C84MP_EQ_HINT `cW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`);
       C84MP_EQ_HINT `sW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`)]]]]);
    (* noWV, first *)
    (MP_TAC(CONJUNCT2(UNDISCH(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
        `--sW`; `cW:real`] C84MP_SUPPORT))) THEN
     REWRITE_TAC[REAL_NEG_NEG] THEN
     ASM_CASES_TAC `sW * cB - cW * sB <= &0` THENL
     [SUBGOAL_THEN `abs(--sW * cB + cW * sB) = --sW * cB + cW * sB /\
                    abs(sW * sB + cW * cB) = sW * sB + cW * cB`
        (fun th -> REWRITE_TAC[th]) THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`(--sW * cB + cW * sB) * ((&33 / &20) * (cB + sB) + &1) <=
         (--sW * cB + cW * sB) * (uB + aB)`;
        `&1 + cB - (&113 / &50) * sB <= vB + aB`;
        `(cW * cB + sW * sB) * (&1 + cB - (&113 / &50) * sB) <= (cW * cB + sW * sB) * (vB + aB)`] THEN
      SUBGOAL_THEN `&0 < (cW * sB - sW * cB) + (cW * cB + sW * sB) * (&1 - (&13 / &20) * cB - (&61 / &100) * sB)`
        ASSUME_TAC THENL
       [ASM_CASES_TAC `&0 < (cW * cB + sW * sB)` THENL
         [NLIN_FACTS_TAC [] [`&0 < (cW * cB + sW * sB) * (&1 - (&13 / &20) * cB - (&61 / &100) * sB)`] THEN
          NLIN_TAC ~deg2:false [];
          SUBGOAL_THEN `(cW * cB + sW * sB) = &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(sW * cB - cW * sB) pow 2 = &1` ASSUME_TAC THENL
           [MAP_EVERY UNDISCH_TAC [`(cW * cB + sW * sB) = &0`; `cB pow 2 + sB pow 2 = &1`;
                                   `cW pow 2 + sW pow 2 = &1`] THEN CONV_TAC REAL_RING;
            ALL_TAC] THEN
          NLIN_TAC []];
        ALL_TAC] THEN
      NLIN_TAC ~deg2:false [C84MP_EQ_HINT `cW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`);
       C84MP_EQ_HINT `sW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`)];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      SUBGOAL_THEN `abs(--sW * cB + cW * sB) = --(--sW * cB + cW * sB) /\
                    abs(sW * sB + cW * cB) = sW * sB + cW * cB`
        (fun th -> REWRITE_TAC[th]) THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`cB:real`; `sB:real`] C84PM_DIAGONAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`(--sW * cB + cW * sB) * (cB * &2 + sB * &457 / &500) < (--sW * cB + cW * sB) * uB`;
        `&1 + cB - (&113 / &50) * sB <= vB + aB`;
        `(cW * cB + sW * sB) * (&1 + cB - (&113 / &50) * sB) <= (cW * cB + sW * sB) * (vB + aB)`] THEN
      SUBGOAL_THEN `&0 < cB * (cB - &13 / &20 - (&13 / &50) * cB * sB - (&43 / &500) * sB pow 2) + sB * (sB - &7 / &20 + (&43 / &500) * cB * sB - (&13 / &50) * sB pow 2)` ASSUME_TAC THENL
       [NLIN_TAC ~deg2:false
         [C84MP_EQ_HINT `&1` (ASSUME `cB pow 2 + sB pow 2 = &1`);
          C84MP_EQ_HINT `sB:real` (ASSUME `cB pow 2 + sB pow 2 = &1`);
          C84MP_EQ_HINT `cB:real` (ASSUME `cB pow 2 + sB pow 2 = &1`)]; ALL_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= (cW - sW) * (cB * (cB - &13 / &20 - (&13 / &50) * cB * sB - (&43 / &500) * sB pow 2) + sB * (sB - &7 / &20 + (&43 / &500) * cB * sB - (&13 / &50) * sB pow 2))`;
        `&0 < (sW * cB - cW * sB) * ((cB - &13 / &20 - (&13 / &50) * cB * sB - (&43 / &500) * sB pow 2) + (sB - &7 / &20 + (&43 / &500) * cB * sB - (&13 / &50) * sB pow 2))`] THEN
      SUBGOAL_THEN `&0 < cW * (cB - &13 / &20 - (&13 / &50) * cB * sB - (&43 / &500) * sB pow 2) + sW * (sB - &7 / &20 + (&43 / &500) * cB * sB - (&13 / &50) * sB pow 2)` ASSUME_TAC THENL
       [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
        NLIN_FACTS_TAC [] [`(cB - sB) * (cW * (cB - &13 / &20 - (&13 / &50) * cB * sB - (&43 / &500) * sB pow 2) + sW * (sB - &7 / &20 + (&43 / &500) * cB * sB - (&13 / &50) * sB pow 2)) <= &0`] THEN
        NLIN_TAC ~deg2:false [];
        ALL_TAC] THEN
      NLIN_TAC ~deg2:false [C84MP_EQ_HINT `cW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`);
       C84MP_EQ_HINT `sW:real` (ASSUME `cB pow 2 + sB pow 2 = &1`)]]);
    (* noWV, second *) NLIN_TAC ~deg2:false []]);;

(* Lean: impossible *)
let C84MP_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cW sW uW vW aW.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aB /\ aB = aW /\
     linside cB sB uB vB aB (&2) (&457 / &500) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     linside cW sW uW vW aW (&33 / &20) (&33 / &20) /\
     linside cW sW uW vW aW (&33 / &20) (&47 / &20) /\
     linside cW sW uW vW aW (&87 / &50) (&2) /\
     ~linside cB sB uB vB aB (&33 / &20) (&33 / &20) /\
     ~linside cB sB uB vB aB (&113 / &50) (&1) /\
     ~linside cB sB uB vB aB (&12 / &5) (&1) /\
     ldisj cB sB uB vB aB cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aW`)) THEN
  UNDISCH_TAC `ldisj cB sB uB vB aB cW sW uW vW aB` THEN REWRITE_TAC[ldisj] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `ab:real = aB` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && not(is_neg(snd(strip_forall(concl th))))
           then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aw:real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `aw:real = aB` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && not(is_neg(snd(strip_forall(concl th))))
           then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC)) THEN
  MP_TAC(SPECL [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`]
    C84MB_CANONICAL_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC C84MP_CANONICAL_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                        `cw:real`; `sw:real`; `uw:real`; `vw:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_REAL_ARITH_TAC);;
