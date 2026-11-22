(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/EndingAxes.lean                      *)
(* (namespace N12Compact.C1092MMMPEndingAxes).                               *)
(* clockwise (c,s,u,v,a) = (c, s, --v - a, u, a).  lower/upper: ABT_lower/  *)
(* ABT_upper; faceSeparation_of_disjoint: CSAT_FACESEPARATION_OF_DISJOINT;   *)
(* separated / parallel_radius / transverse_radius / strict_bounds / ownU:   *)
(* the ABT_ lemmas of ABTransverse.ml.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: clockwise (definition) and its OpenSquare invariants *)
let C1092MEA_CLOCKWISE_SQUARE = prove
 (`forall c s u v a. lsquare c s u v a ==> lsquare c s (--v - a) u a`,
  REWRITE_TAC[lsquare]);;

(* Lean: inside_clockwise *)
let C1092MEA_INSIDE_CLOCKWISE = prove
 (`forall c s u v a x y. linside c s (--v - a) u a x y <=> linside c s u v a y (--x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: upper_nn *)
let C1092MEA_UPPER_NN = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ &0 <= e
     ==> ABT_upper c s u v a nx ny = d * (u + a) + e * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`] THEN REAL_ARITH_TAC);;

let C1092MEA_BOUND_TAC sq x y nx ny =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC];;

let C1092MEA_SEP_TAC sqs nx ny rad =
  MP_TAC(SPECL (sqs @ [nx; ny]) ABT_SEPARATED) THEN
  ANTS_TAC THENL
   [MP_TAC rad THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: alternatives *)
let C1092MEA_ALTERNATIVES = prove
 (`forall cW sW uW vW aW cN sN uN vN aN.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     aW = aN /\
     &0 < cW /\ &0 <= sW /\ sW <= cW /\ &0 < cN /\ &0 <= sN /\ sN <= cN /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
     ldisj cW sW uW vW aW cN sN uN vN aN
     ==> uW + aW <= ABT_lower cN sN uN vN aN cW sW \/
         ABT_upper cW sW uW vW aW cN sN <= uN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ASM_REWRITE_TAC[C977CB_faceSep] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  let sW5 = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
  and sN5 = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] in
  let sqs = sW5 @ sN5 in
  let bounds nx ny =
    C1092MEA_BOUND_TAC sW5 `--(&7 / &20)` `&7 / &20` nx ny THEN
    C1092MEA_BOUND_TAC sN5 `&7 / &20` `&7 / &20` nx ny THEN
    C1092MEA_BOUND_TAC sW5 `&0` `&0` nx ny in
  let case nx ny rad =
    C1092MEA_SEP_TAC sqs nx ny rad THEN bounds nx ny THEN ASM_REAL_ARITH_TAC in
  let w6 = [`cW:real`; `sW:real`; `aW:real`; `cN:real`; `sN:real`; `aW:real`]
  and n6 = [`cN:real`; `sN:real`; `aW:real`; `cW:real`; `sW:real`; `aW:real`] in
  FIRST [case `cW:real` `sW:real` (SPECL w6 ABT_PARALLEL_RADIUS);
         case `--sW:real` `cW:real` (SPECL w6 ABT_TRANSVERSE_RADIUS);
         case `cN:real` `sN:real` (SPECL n6 ABT_PARALLEL_RADIUS);
         case `--sN:real` `cN:real` (SPECL n6 ABT_TRANSVERSE_RADIUS)]);;
