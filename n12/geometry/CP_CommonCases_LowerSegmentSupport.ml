(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/LowerSegmentSupport.lean           *)
(* (N12Compact.CommonCases.LowerSegmentSupport).                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SegmentCorner.ml";;

(* Lean: support *)
let CCLSS_SUPPORT = prove
 (`forall lU hU lV hV u0 v0 u1 v1.
     u0 <= lU /\ lU < u1 /\ u1 < hU /\ lV < v0 /\ v0 < hV /\ v1 <= lV /\
     (forall t. &0 <= t ==> t <= &1 ==>
        ~(lU < (&1 - t) * u0 + t * u1 /\ (&1 - t) * u0 + t * u1 < hU /\
          lV < (&1 - t) * v0 + t * v1 /\ (&1 - t) * v0 + t * v1 < hV))
     ==> (v0 - v1) * u0 + (u1 - u0) * v0 <= (v0 - v1) * lU + (u1 - u0) * lV`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lU:real`; `hU:real`; `--hV`; `--lV`; `u0:real`; `--v0`;
                `u1:real`; `--v1`] SEGC_CROSSING_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;
