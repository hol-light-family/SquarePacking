(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryBarCrosspoint/Inputs.lean   *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint).      *)
(* LowerSegmentSupport.support: CCLSS_SUPPORT.  The OpenSquare invariants   *)
(* are explicit hypotheses c * c + s * s = &1, &0 < a.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_LowerSegmentSupport.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: Input (structure) *)
let obci_input = new_definition
 `obci_input c s u v a <=>
    &1 < a /\
    linside c s u v a (&7 / &20) (--(&7 / &20)) /\
    linside c s u v a (&1) (--(&13 / &50)) /\
    linside c s u v a (&1) (--(&2 / &5)) /\
    ~linside c s u v a (&543 / &500) (&0) /\
    ~linside c s u v a (&543 / &500) (--(&1)) /\
    (forall x. &13 / &50 <= x ==> x <= &22 / &25 ==> ~linside c s u v a x (--(&1)))`;;

(* Lean: Input.reframe *)
let OBCI_INPUT_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar.
     obci_input c s u v a /\ ar = a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> obci_input cr sr ur vr ar`,
  REPEAT GEN_TAC THEN REWRITE_TAC[obci_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_segment *)
let OBCI_POSITIVE_SEGMENT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a /\
     (&13 / &50) * c - s <= u /\
     v < --(&13 / &50) * s - c /\ --(&13 / &50) * s - c < v + a /\
     u < (&22 / &25) * c - s /\ (&22 / &25) * c - s < u + a /\
     --(&22 / &25) * s - c <= v
     ==> --(&1) <= s * u + c * v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[obci_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `u + a:real`; `v:real`; `v + a:real`;
                `(&13 / &50) * c - s`; `--(&13 / &50) * s - c`;
                `(&22 / &25) * c - s`; `--(&22 / &25) * s - c`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - w) * &13 / &50 + w * &22 / &25` o
      check (fun th -> is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[linside] THEN MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&31 / &50) * (c * c + s * s) = &31 / &50` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: negative_segment *)
let OBCI_NEGATIVE_SEGMENT = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a /\ s = --t /\
     u < (&13 / &50) * c + t /\ (&13 / &50) * c + t < u + a /\
     (&13 / &50) * t - c <= v /\
     u + a <= (&22 / &25) * c + t /\
     v < (&22 / &25) * t - c /\ (&22 / &25) * t - c < v + a
     ==> --(&1) <= --t * (u + a) + c * v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[obci_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  MP_TAC(SPECL [`--(u + a)`; `--u:real`; `v:real`; `v + a:real`;
                `--((&22 / &25) * c + t)`; `(&22 / &25) * t - c`;
                `--((&13 / &50) * c + t)`; `(&13 / &50) * t - c`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - w) * &22 / &25 + w * &13 / &50` o
      check (fun th -> is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[linside] THEN MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&31 / &50) * (c * c + --t * --t) = &31 / &50` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  REAL_ARITH_TAC);;
