(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4OuterMidpoint.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C983.F4OuterMidpoint).       *)
(* The outer-midpoint theorem.  Squares W = cW sW uW vW aW, E = cE sE uE vE  *)
(* aE.  F4BottomMidpoint.SoutheastData: f4bm_southeast_data; F4OuterScalars:*)
(* C983F4O_*; upper / lower: ABT_upper / ABT_lower with face forms          *)
(* OCSB_LOWER_PN, C1092TFSU_UPPER_POS_NEG, C1092TFSU_UPPER_POS_POS; the SAT *)
(* reduction: ABT_FOUR_AXES; canonical_frame: CLF_CANONICAL_FRAME.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4BottomMidpoint.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4OuterScalars.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

(* Lean: Input (structure) *)
let c983f4om_input = new_definition
 `c983f4om_input (cW:real) sW uW vW aW (cE:real) sE uE vE aE (t:real) <=>
    f4bm_southeast_data cE sE uE vE aE t /\ aW = aE /\ t / (&1 + cE) < &3 / &20 /\
    &13 / &50 * t <= uE /\
    linside cE sE uE vE aE (&1 / &2) (&0) /\
    linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    linside cW sW uW vW aW (&0) (--(&13 / &50)) /\
    linside cW sW uW vW aW (&0) (&0) /\
    ~linside cW sW uW vW aW (&0) (&13 / &50) /\
    ~linside cW sW uW vW aW (--(&1)) (&13 / &50) /\
    ~linside cW sW uW vW aW (--(&1)) (--(&2 / &5)) /\
    ldisj cW sW uW vW aW cE sE uE vE aE`;;

let C983F4OM_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (can (find_term ((=) `linside`)) t && not (mem t keep))
    then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let C983F4OM_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN C983F4OM_KEEP_TAC keep; ALL_TAC];;

let C983F4OM_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C983F4OM_SQS = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`];;

(* unfold the input; E's sine is --t; the common side is aE *)
let C983F4OM_SETUP_TAC =
  REWRITE_TAC[IMP_CONJ; c983f4om_input; f4bm_southeast_data] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`));;

let f4omMk = `linside cE (--t) uE vE aE (&7 / &20) (--(&7 / &20))`
and f4omEl = `linside cE (--t) uE vE aE (&13 / &50) (&0)`
and f4omOu = `linside cE (--t) uE vE aE (&1) (--(&13 / &50))`
and f4omEx = `linside cE (--t) uE vE aE (&1 / &2) (&0)`
and f4omSw = `linside cW sW uW vW aE (--(&7 / &20)) (--(&7 / &20))`
and f4omNw = `linside cW sW uW vW aE (--(&7 / &20)) (&7 / &20)`
and f4omIn = `linside cW sW uW vW aE (&0) (--(&13 / &50))`
and f4omCe = `linside cW sW uW vW aE (&0) (&0)`;;

(* Lean: missing_faces (private) *)
let C983F4OM_MISSING_FACES = prove
 (`forall cW sW uW vW aW cE sE uE vE aE t.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      c983f4om_input cW sW uW vW aW cE sE uE vE aE t /\
      ~linside cE sE uE vE aE (&1) (--(&1 / &2))
      ==> uE < cE + t / &2 - &1 /\ uE < &42 / &409 /\
          linside cE sE uE vE aE (&0) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN C983F4OM_SETUP_TAC THEN
  SUBGOAL_THEN `cE <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `cE * cE + --t * --t = &1` THEN DISCH_TAC THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  C983F4OM_STEP `uE + aE <= cE + t / &2` [`~linside cE (--t) uE vE aE (&1) (--(&1 / &2))`; f4omMk; f4omOu] THEN
  MP_TAC(SPECL [`cE:real`; `t:real`] C983F4O_OUTER_CAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cE * cE + --t * --t = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; C983F4OM_KEEP_TAC [f4omEl]]);;

(* Lean: positive_faces (private) *)
let C983F4OM_POSITIVE_FACES = prove
 (`forall cW sW uW vW aW cE sE uE vE aE t.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      c983f4om_input cW sW uW vW aW cE sE uE vE aE t /\
      &0 < cW /\ &0 <= sW /\ sW <= cW /\
      ~linside cW sW uW vW aW (&0) (--(&1 / &2))
      ==> --(cW / &2) <= vW /\ uW + aW <= &13 / &50 * sW /\
          vW + aW <= sW + &13 / &50 * cW /\ &13 / &50 < sW`,
  REPEAT GEN_TAC THEN C983F4OM_SETUP_TAC THEN
  SUBGOAL_THEN `cW <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `sW:real` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN DISCH_TAC THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  C983F4OM_STEP `--(cW / &2) <= vW` [`~linside cW sW uW vW aE (&0) (--(&1 / &2))`; f4omSw; f4omIn] THEN
  C983F4OM_STEP `uW + aE <= &13 / &50 * sW` [`~linside cW sW uW vW aE (&0) (&13 / &50)`; f4omIn; f4omNw] THEN
  C983F4OM_STEP `vW + aE <= sW + &13 / &50 * cW`
    [`~linside cW sW uW vW aE (--(&1)) (&13 / &50)`; f4omIn; f4omSw] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] C983F4O_POSITIVE_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: negative_faces (private; sW = --r) *)
let C983F4OM_NEGATIVE_FACES = prove
 (`forall cW sW uW vW aW cE sE uE vE aE t r.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      c983f4om_input cW sW uW vW aW cE sE uE vE aE t /\
      sW = --r /\ &0 < cW /\ &0 <= r /\ r <= cW /\
      ~linside cW sW uW vW aW (&0) (--(&1 / &2))
      ==> vW + aW <= &13 / &50 * cW /\ uW + aW <= r / &2 /\ &39 / &100 < r`,
  REPEAT GEN_TAC THEN C983F4OM_SETUP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --r`)) THEN
  let f4omSw = `linside cW (--r) uW vW aE (--(&7 / &20)) (--(&7 / &20))`
  and f4omNw = `linside cW (--r) uW vW aE (--(&7 / &20)) (&7 / &20)`
  and f4omIn = `linside cW (--r) uW vW aE (&0) (--(&13 / &50))` in
  SUBGOAL_THEN `cW <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `r:real` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `cW * cW + --r * --r = &1` THEN DISCH_TAC THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  C983F4OM_STEP `vW + aE <= &13 / &50 * cW` [`~linside cW (--r) uW vW aE (&0) (&13 / &50)`; f4omNw; f4omIn; f4omSw] THEN
  C983F4OM_STEP `uW + aE <= r / &2` [`~linside cW (--r) uW vW aE (&0) (--(&1 / &2))`; f4omIn] THEN
  SUBGOAL_THEN `&9 / &100 * cW < &7 / &20 * r` ASSUME_TAC THENL
   [C983F4OM_KEEP_TAC [f4omNw]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cW <= &1 - r * r / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `cW - &1` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `cW * cW + --r * --r = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C983F4OM_PROD `&0 <= (&39 / &100 - r) * (&1 - &33 / &100 * (r + &39 / &100))` THEN
  SUBGOAL_THEN `&33 / &50 * cW + r < &1` ASSUME_TAC THENL
   [C983F4OM_KEEP_TAC []; ALL_TAC] THEN
  C983F4OM_STEP `--cW + &2 / &5 * r <= uW` [`~linside cW (--r) uW vW aE (--(&1)) (--(&2 / &5))`; f4omSw] THEN
  C983F4OM_PROD `&0 < (cW + r / &10 - &1) * (cW + r / &10 + &1)` THEN
  C983F4OM_PROD `&0 < r * (&7 / &20 * r - &9 / &100 * cW)` THEN
  MP_TAC(SPEC `r:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C983F4OM_KEEP_TAC []);;

(* Lean: positive_normals (private) *)
let C983F4OM_POSITIVE_NORMALS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE t.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      c983f4om_input cW sW uW vW aW cE sE uE vE aE t /\
      &0 < cW /\ &0 <= sW /\ sW <= cW /\
      ~linside cW sW uW vW aW (&0) (--(&1 / &2)) /\ uE < &42 / &409
      ==> ABT_lower cE sE uE vE aE sW (--cW) < ABT_upper cW sW uW vW aW sW (--cW) /\
          ABT_lower cE sE uE vE aE cE sE < ABT_upper cW sW uW vW aW cE sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C983F4OM_SQS C983F4OM_POSITIVE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `c983f4om_input cW sW uW vW aW cE sE uE vE aE t` THEN C983F4OM_SETUP_TAC THEN
  SUBGOAL_THEN `cE <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `cE * cE + --t * --t = &1` THEN DISCH_TAC THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  C983F4OM_PROD `&0 <= t * (cW - sW)` THEN C983F4OM_PROD `&0 < cW * (cE - t)` THEN
  C983F4OM_PROD `&0 < cE * sW` THEN C983F4OM_PROD `&0 < t * cW` THEN
  C983F4OM_PROD `&0 <= cE * (cW - sW)` THEN C983F4OM_PROD `&0 <= cW * (&2 - cE - t)` THEN
  SUBGOAL_THEN `&0 < cE * cW - t * sW /\ &0 < cE * sW + t * cW /\
                cE * sW + t * cW <= &2 * cW` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
    OCSB_LOWER_PN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C983F4OM_PROD `&0 < (cE * sW + t * cW) * (&42 / &409 - uE)` THEN
  SUBGOAL_THEN `&0 < vE + aE` ASSUME_TAC THENL [C983F4OM_KEEP_TAC [f4omEx]; ALL_TAC] THEN
  C983F4OM_PROD `&0 < (cE * cW - t * sW) * (vE + aE)` THEN
  ABT_SB_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aE:real`]
    `&0` `--(&13 / &50)` `sW:real` `--cW` THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aE:real`; `cE:real`; `--t`;
                `cE * cW - t * sW`; `--(cE * sW + t * cW)`] C1092TFSU_UPPER_POS_NEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `t:real`; `cW:real`; `sW:real`; `uW + aE`; `vW:real`]
    C983F4O_POSITIVE_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC; C983F4OM_KEEP_TAC [f4omCe; f4omIn]]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THEN ABT_ARITH_TAC);;

(* Lean: negative_normals (private; sW = --r) *)
let C983F4OM_NEGATIVE_NORMALS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE t r.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      c983f4om_input cW sW uW vW aW cE sE uE vE aE t /\
      sW = --r /\ &0 < cW /\ &0 <= r /\ r <= cW /\
      ~linside cW sW uW vW aW (&0) (--(&1 / &2)) /\
      uE < cE + t / &2 - &1 /\ uE < &42 / &409
      ==> ABT_lower cE sE uE vE aE cW sW < ABT_upper cW sW uW vW aW cW sW /\
          ABT_lower cE sE uE vE aE cE sE < ABT_upper cW sW uW vW aW cE sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C983F4OM_SQS @ [`r:real`]) C983F4OM_NEGATIVE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `c983f4om_input cW sW uW vW aW cE sE uE vE aE t` THEN C983F4OM_SETUP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --r`)) THEN
  SUBGOAL_THEN `t < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cW < cE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (r - t) * (r + t) /\ &0 <= (cW - cE) * (cW + cE)` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `cW * cW + --r * --r = &1` THEN UNDISCH_TAC `cE * cE + --t * --t = &1` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  C983F4OM_PROD `&0 < cE * cW` THEN C983F4OM_PROD `&0 < t * r` THEN
  C983F4OM_PROD `&0 < cE * (r - t)` THEN C983F4OM_PROD `&0 < t * (cE - cW)` THEN
  SUBGOAL_THEN `&0 < cE * cW + t * r /\ &0 < cE * r - t * cW` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`; `cW:real`; `--r`]
    OCSB_LOWER_PN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C983F4OM_PROD `&0 < (cE * cW + t * r) * ((cE + t / &2 - &1) - uE)` THEN
  SUBGOAL_THEN `&0 < vE + aE - t / &2` ASSUME_TAC THENL [C983F4OM_KEEP_TAC [f4omEx]; ALL_TAC] THEN
  C983F4OM_PROD `&0 < (cE * r - t * cW) * (vE + aE - t / &2)` THEN
  MP_TAC(SPECL [`cE:real`; `t:real`; `cW:real`; `r:real`] C983F4O_NEGATIVE_OWN_SUPPORT) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `cE * cE + --t * --t = &1` THEN UNDISCH_TAC `cW * cW + --r * --r = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--r`; `uW:real`; `vW:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&13 / &50 * r < uW + aE` ASSUME_TAC THENL
   [C983F4OM_KEEP_TAC [`linside cW (--r) uW vW aE (&0) (--(&13 / &50))`]; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &20 * (cW - r) < vW + aE` ASSUME_TAC THENL
   [C983F4OM_KEEP_TAC [`linside cW (--r) uW vW aE (--(&7 / &20)) (&7 / &20)`]; ALL_TAC] THEN
  CONJ_TAC THENL [ABT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--r`; `uW:real`; `vW:real`; `aE:real`; `cE:real`; `--t`;
                `cE * cW + t * r`; `cE * r - t * cW`] C1092TFSU_UPPER_POS_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C983F4OM_PROD `&0 < (cE * cW + t * r) * ((uW + aE) - &13 / &50 * r)` THEN
  C983F4OM_PROD `&0 < (cE * r - t * cW) * ((vW + aE) - &7 / &20 * (cW - r))` THEN
  MP_TAC(SPECL [`cE:real`; `t:real`; `cW:real`; `r:real`] C983F4O_NEGATIVE_SUPPORT) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `cE * cE + --t * --t = &1` THEN UNDISCH_TAC `cW * cW + --r * --r = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&13 / &50 * (cE * cW + t * r) * r + &7 / &20 * (cE * r - t * cW) * (cW - r) =
      cE * (&61 / &100 * cW * r - &7 / &20 * r pow 2) +
      t * (&61 / &100 * r pow 2 + &7 / &20 * cW * r - &7 / &20)` ASSUME_TAC THENL
   [UNDISCH_TAC `cW * cW + --r * --r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABT_ARITH_TAC);;

(* the cone of separating directions (Lean: cone, local to inside) *)
let C983F4OM_CONE = prove
 (`forall cW sW uW vW cE sE uE vE a nx ny.
      cW * cW + sW * sW = &1 /\ cE * cE + sE * sE = &1 /\ &0 < a /\
      linside cW sW uW vW a (--(&7 / &20)) (--(&7 / &20)) /\
      linside cW sW uW vW a (&0) (--(&13 / &50)) /\
      linside cE sE uE vE a (&7 / &20) (--(&7 / &20)) /\
      linside cE sE uE vE a (&0) (--(&1 / &2)) /\
      nx pow 2 + ny pow 2 = &1 /\
      ABT_upper cW sW uW vW a nx ny <= ABT_lower cE sE uE vE a nx ny
      ==> &0 < nx /\ ny < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_SB_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`]
    `--(&7 / &20)` `--(&7 / &20)` `nx:real` `ny:real` THEN
  ABT_SB_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`]
    `&0` `--(&13 / &50)` `nx:real` `ny:real` THEN
  ABT_SB_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`]
    `&7 / &20` `--(&7 / &20)` `nx:real` `ny:real` THEN
  ABT_SB_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`]
    `&0` `--(&1 / &2)` `nx:real` `ny:real` THEN
  ABT_ARITH_TAC);;

(* Lean: reverse (local to inside) *)
let C983F4OM_REVERSE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE nx ny.
      ABT_upper cE sE uE vE aE nx ny <= ABT_lower cW sW uW vW aW nx ny
      ==> ABT_upper cW sW uW vW aW (--nx) (--ny) <= ABT_lower cE sE uE vE aE (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

let c983f4om_pn = MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                         `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
                    C983F4OM_POSITIVE_NORMALS) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
           ASM_REAL_ARITH_TAC;;
let c983f4om_nn = MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                         `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`; `--s1`]
                    C983F4OM_NEGATIVE_NORMALS) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
           ASM_REAL_ARITH_TAC;;
let c983f4om_cone nx ny =
    FIRST_X_ASSUM(MP_TAC o SPECL [nx; ny] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ABT_upper`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC];;
let c983f4om_rev =
    FIRST_X_ASSUM(MP_TAC o
      (fun th -> MATCH_MP (SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                         `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C983F4OM_REVERSE) th) o
      check (fun th -> try let l, r = dest_binary "real_le" (concl th) in
                           rator(rator l) = `ABT_upper cE sE uE vE aE` &&
                           rator(rator r) = `ABT_lower c1 s1 u1 v1 aE`
                       with _ -> false)) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC;;

(* Lean: inside *)
let C983F4OM_INSIDE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE t.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      c983f4om_input cW sW uW vW aW cE sE uE vE aE t
      ==> linside cE sE uE vE aE (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPECL C983F4OM_SQS C983F4OM_MISSING_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aW`)) THEN
  SUBGOAL_THEN `c983f4om_input c1 s1 u1 v1 aW cE sE uE vE aE t` ASSUME_TAC THENL
   [UNDISCH_TAC `c983f4om_input cW sW uW vW aW cE sE uE vE aE t` THEN
    REWRITE_TAC[c983f4om_input; ldisj] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `c983f4om_input cW sW uW vW aW cE sE uE vE aE t`)) THEN
  SUBGOAL_THEN `~linside c1 s1 u1 v1 aW (&0) (--(&1 / &2))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[c983f4om_input; ldisj] o
      check (fun th -> concl th = `c983f4om_input c1 s1 u1 v1 aW cE sE uE vE aE t`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `--(&1 / &2)`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the facts needed below, extracted from the input *)
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    REWRITE_RULE[c983f4om_input; f4bm_southeast_data] o
    check (fun th -> concl th = `c983f4om_input c1 s1 u1 v1 aW cE sE uE vE aE t`)) THEN
  SUBGOAL_THEN `sE < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `sE = --t`)) THEN
  SUBGOAL_THEN `forall nx ny. nx pow 2 + ny pow 2 = &1 /\
      ABT_upper c1 s1 u1 v1 aE nx ny <= ABT_lower cE sE uE vE aE nx ny
      ==> &0 < nx /\ ny < &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `cE:real`; `sE:real`;
                  `uE:real`; `vE:real`; `aE:real`; `nx:real`; `ny:real`] C983F4OM_CONE) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aW:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_CASES_TAC `&0 <= s1` THENL [c983f4om_cone `c1:real` `s1:real`; c983f4om_nn];
    c983f4om_rev THEN c983f4om_cone `--c1` `--s1`;
    c983f4om_cone `--s1` `c1:real`;
    c983f4om_rev THEN ASM_CASES_TAC `&0 <= s1` THENL [c983f4om_pn; c983f4om_cone `s1:real` `--c1`];
    ASM_CASES_TAC `&0 <= s1` THENL [c983f4om_pn; c983f4om_nn];
    c983f4om_rev THEN c983f4om_cone `--cE` `--sE`;
    c983f4om_cone `--sE` `cE:real`;
    c983f4om_rev THEN c983f4om_cone `sE:real` `--cE`]);;
