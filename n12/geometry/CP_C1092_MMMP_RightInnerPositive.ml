(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/RightInnerPositive.lean              *)
(* (namespace N12Compact.C1092MMMPRightInnerPositive).                       *)
(* faceSeparation_of_disjoint: CSAT_FACESEPARATION_OF_DISJOINT; separated,  *)
(* parallel_radius, transverse_radius, strict_bounds, ownU, ownV: ABT_*;     *)
(* formulas / upper_np: C1092WS_*; exists_negative / Data: C1092MRIP_*.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightInwardProfile.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

let C1092MRIPOS_BOUND_TAC sq x y nx ny =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC];;

let C1092MRIPOS_SEP_TAC sqs nx ny rad =
  MP_TAC(SPECL (sqs @ [nx; ny]) ABT_SEPARATED) THEN
  ANTS_TAC THENL
   [MP_TAC rad THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: axes (private) *)
let C1092MRIPOS_AXES = prove
 (`forall cE sE uE vE aE cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     aE = aR /\ &0 < cE /\ &0 <= sE /\ &0 < cR /\ sR <= &0 /\
     linside cE sE uE vE aE (&7 / &20) (&7 / &20) /\
     linside cE sE uE vE aE (&13 / &50) (&1) /\
     linside cR sR uR vR aR (&13 / &50) (&0) /\
     linside cR sR uR vR aR (&1) (&2 / &5) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> ABT_upper cR sR uR vR aR (--sE) cE <= vE \/
         ABT_upper cE sE uE vE aE cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aR`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ASM_REWRITE_TAC[C977CB_faceSep] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  let sE5 = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
  and sR5 = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`] in
  let sqs = sE5 @ sR5 in
  let bounds nx ny =
    C1092MRIPOS_BOUND_TAC sE5 `&7 / &20` `&7 / &20` nx ny THEN
    C1092MRIPOS_BOUND_TAC sE5 `&13 / &50` `&1` nx ny THEN
    C1092MRIPOS_BOUND_TAC sR5 `&13 / &50` `&0` nx ny THEN
    C1092MRIPOS_BOUND_TAC sR5 `&1` `&2 / &5` nx ny in
  let case nx ny rad =
    C1092MRIPOS_SEP_TAC sqs nx ny rad THEN bounds nx ny THEN ASM_REAL_ARITH_TAC in
  let e6 = [`cE:real`; `sE:real`; `aE:real`; `cR:real`; `sR:real`; `aE:real`]
  and r6 = [`cR:real`; `sR:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`] in
  FIRST [case `cE:real` `sE:real` (SPECL e6 ABT_PARALLEL_RADIUS);
         case `--sE:real` `cE:real` (SPECL e6 ABT_TRANSVERSE_RADIUS);
         case `cR:real` `sR:real` (SPECL r6 ABT_PARALLEL_RADIUS);
         case `--sR:real` `cR:real` (SPECL r6 ABT_TRANSVERSE_RADIUS)]);;

(* Lean: fixed (private) *)
let C1092MRIPOS_FIXED = prove
 (`forall cE sE uE vE aE cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aE /\ aE = aR /\ c977cc_normal cE sE /\ c977cc_normal cR (--sR) /\
     c1092mrip_data cR sR uR vR aR /\
     linside cE sE uE vE aE (&7 / &20) (&7 / &20) /\
     linside cE sE uE vE aE (&13 / &50) (&1) /\
     linside cE sE uE vE aE (&2 / &5) (&1) /\
     linside cR sR uR vR aR (&13 / &50) (&0) /\
     linside cR sR uR vR aR (&1) (&2 / &5) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    C1092MRIPOS_AXES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cR (--sR)`)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; c1092mrip_data] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th) ||
                     can (term_match [] `c1092mrip_data c s u v a`) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aR`)) THEN
  ABBREV_TAC `t = --sR` THEN
  SUBGOAL_THEN `sR = --t` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cR * cE - t * sE /\ &0 < cR * sE + t * cE` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (cR - t) * cE /\ &0 <= t * (cE - sE) /\
                  &0 <= cR * sE /\ &0 < t * cE` MP_TAC THENL
     [REPEAT CONJ_TAC THEN
      (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aE:real`;
                  `--sE:real`; `cE:real`; `--(cR * sE + t * cE)`; `cR * cE - t * sE`]
      C1092WS_UPPER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&0 < (cR * sE + t * cE) * ((&13 / &50) * cR - uR) /\
      &0 < (cR * cE - t * sE) * ((vR + aE) - (&1 + t - (&13 / &50) * cR)) /\
      &0 <= cR * t /\ &0 < (&1 / &3 - t) * (&1 / &3 + t)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&33 / &100 < cR + (&37 / &50) * cR * t - (&13 / &50) * cR pow 2 - &7 / &20 /\
      --(&33 / &100) < &9 / &100 - t - (&37 / &50) * t pow 2 + (&13 / &50) * cR * t`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < cE * ((cR + (&37 / &50) * cR * t - (&13 / &50) * cR pow 2 - &7 / &20) -
                 &33 / &100) /\
      &0 <= sE * ((&9 / &100 - t - (&37 / &50) * t pow 2 + (&13 / &50) * cR * t) +
                  &33 / &100)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `--(cR * sE + t * cE) * ((&13 / &50) * cR) +
      (cR * cE - t * sE) * (&1 + t - (&13 / &50) * cR) - (&7 / &20) * (cE - sE) =
      cE * (cR + (&37 / &50) * cR * t - (&13 / &50) * cR pow 2 - &7 / &20) +
      sE * (&9 / &100 - t - (&37 / &50) * t pow 2 + (&13 / &50) * cR * t)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `cR pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `--t:real`] C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cR * cE + --t * sE = cR * cE - t * sE /\
                --cR * sE + --t * cE = --(cR * sE + t * cE)`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> max x (&0) = x`;
               REAL_ARITH `&0 < x ==> max (--x) (&0) = &0`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < (cR * cE - t * sE) * ((uE + aE) - (cE * &2 / &5 + sE * &1)) /\
    &0 < (cR * sE + t * cE) * ((--sE * &7 / &20 + cE * &7 / &20) - vE) /\
    &0 <= cE * sE /\ &0 <= sE * (cE - sE)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < ((&13 / &37) * cR - t) * (&7 / &20 + (&7 / &10) * cE * sE) /\
    &0 <= (cR / &20 + (&13 / &20) * t) * (sE * (cE - sE)) /\
    &0 < cR * (&63 / &3700 + (&131 / &370) * cE * sE)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cR * cE - t * sE) * ((&2 / &5) * cE + sE) -
    (cR * sE + t * cE) * (&7 / &20) * (cE - sE) - (&13 / &50) * cR =
    cR * (&7 / &50 - sE pow 2 / &20 + (&13 / &20) * cE * sE) -
    t * (&7 / &20 + (&13 / &20) * sE pow 2 + cE * sE / &20)` ASSUME_TAC THENL
   [UNDISCH_TAC `cE pow 2 + sE pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible *)
let C1092MRIPOS_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cW sW uW vW aW.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aE /\ aE = aW /\ c977cc_normal cE sE /\
     linside cE sE uE vE aE (&7 / &20) (&7 / &20) /\
     linside cE sE uE vE aE (&13 / &50) (&1) /\
     linside cE sE uE vE aE (&2 / &5) (&1) /\
     linside cW sW uW vW aW (&13 / &50) (&0) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&2 / &5) /\
     ~linside cW sW uW vW aW (&1) (--(&13 / &50)) /\
     ldisj cE sE uE vE aE cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aW`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1092MRIP_EXISTS_NEGATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ldisj cE sE uE vE aW cW sW uW vW aW` THEN
    REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&7 / &20`; `&7 / &20`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aW:real`;
                `c':real`; `s':real`; `u':real`; `v':real`; `a':real`]
    C1092MRIPOS_FIXED) THEN
  ASM_REWRITE_TAC[ldisj] THEN
  UNDISCH_TAC `ldisj cE sE uE vE aW cW sW uW vW aW` THEN
  REWRITE_TAC[ldisj] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;
