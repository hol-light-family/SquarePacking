(* ========================================================================= *)
(* Port of Compact/Geometry/MergedLeftEscape.lean                            *)
(* (N12Compact.MergedLeftEscape).  Face reductions for a square owning both  *)
(* left central markers.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: center_cap *)
let MLE_CENTER_CAP = prove
 (`forall c s u v a.
      &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&2) (&2)
      ==> u + a <= &2 * (c + s)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: upper_v *)
let MLE_UPPER_V = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      u + a <= &2 * (c + s) /\
      ~linside c s u v a (&1) (&113 / &50)
      ==> v + a <= (&113 / &50) * c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: left_aux_faces *)
let MLE_LEFT_AUX_FACES = prove
 (`forall c s u v a.
      &0 < c /\ &0 <= s /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&1) (&87 / &50)
      ==> c + (&87 / &50) * s <= u \/ v + a <= (&87 / &50) * c - s`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inward_aux_faces *)
let MLE_INWARD_AUX_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      u + a <= &2 * (c + s) /\
      ~linside c s u v a (&2) (&87 / &50)
      ==> u + a <= &2 * c + (&87 / &50) * s \/
          (&87 / &50) * c - &2 * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
