(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallMarker.lean (Jatloe, N12-jatloe;     *)
(* namespace N12Compact.PositiveWallMarker).  The genuine upper marker       *)
(* restricts a positive left-wall square.  Normal is c977cc_normal;          *)
(* PositiveWallUpperUPositiveLeft.impossible_relaxed / marker_cap are        *)
(* PWUUPL_IMPOSSIBLE_RELAXED / PWUUPL_MARKER_CAP; O.s = -t is sO = --t.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/PositiveWallUpperUPositiveLeft.ml";;

(* Lean: upper_faces *)
let PWM_UPPER_FACES = prove
 (`forall c s u v a.
     c977cc_normal c s /\ linside c s u v a (&457 / &500) (&2) /\
     ~linside c s u v a (&457 / &500) (&3)
     ==> u + a <= (&457 / &500) * c + &3 * s \/ v + a <= &3 * c - (&457 / &500) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  MP_TAC(ASSUME `linside c s u v a (&457 / &500) (&2)`) THEN
  MP_TAC(ASSUME `~linside c s u v a (&457 / &500) (&3)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: upper_v *)
let PWM_UPPER_V = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cL sL /\ c977cc_normal cW sW /\
     &0 < t /\ t <= &1 / &5 /\ aO = aL /\ aL = aW /\ &1 < aL /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     t * (uO + aO) <= cO * vO /\
     uO + aO <= &2 * cO - (&457 / &500) * t /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ~linside cW sW uW vW aW (&457 / &500) (&3) /\
     ldisj cO sO uO vO aO cL sL uL vL aL /\
     ldisj cL sL uL vL aL cW sW uW vW aW
     ==> vW + aW <= &3 * cW - (&457 / &500) * sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] PWM_UPPER_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] PWUUPL_MARKER_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  MATCH_MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    PWUUPL_IMPOSSIBLE_RELAXED) THEN
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]);;
