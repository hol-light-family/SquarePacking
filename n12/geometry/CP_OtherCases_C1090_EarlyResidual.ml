(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/EarlyResidual.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Early; Lean header:     *)
(* "Uncompiled").  The boundary between C1090's early reductions and the     *)
(* continuous residual ending: Early.PointTable (c1090es_pointTable) plus    *)
(* S's G6 and E's F7 gives Residual.Input (c1090ro_input).  q : Fin 12 ->    *)
(* OpenSquare as in EarlySelection.ml / ResidualOwners.ml (unit normals as   *)
(* the hypothesis !i. i < 12 ==> qc i * qc i + qs i * qs i = &1).            *)
(* Residual.impossible = C1090RE_IMPOSSIBLE.  Tag C1090ER_.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1090_EarlySelection.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualEnding.ml";;

(* Lean: residual_input *)
let C1090ER_RESIDUAL_INPUT = prove
 (`forall qc qs qu qv qa.
     c1090es_pointTable qc qs qu qv qa /\
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3)
     ==> c1090ro_input qc qs qu qv qa`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1090es_pointTable; c1090eg_input] THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  REWRITE_TAC[c1090ro_input] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
    check (fun th -> is_forall(concl th) && free_in `(qc:num->real) 8` (concl th))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: residual_impossible *)
let C1090ER_RESIDUAL_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa /\
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1090ER_RESIDUAL_INPUT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1090ES_POINT_TABLE THEN ASM_REWRITE_TAC[]);;
