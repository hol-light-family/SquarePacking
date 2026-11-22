(* ========================================================================= *)
(* Port of Compact/Geometry/EndpointHighRight.lean                           *)
(* The structure Premises becomes the hypothesis list (lsquare = OpenSquare). *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/EndpointRowTemplate.ml";;

(* Lean: impossible *)
let EHR_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\
     lsquare cL sL uL vL aL /\ lsquare cR sR uR vR aR /\
     &1 < aA /\ &1 < aB /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&87 / &50) (&2) /\
     linside cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&3) (&5 / &2) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  ERT_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
  ERT_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `&3`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&5 / &2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aq:real = aA` o concl)) THEN
  FST_STEP(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aA:real`] FSAN_POINT_OF_HIGHER_R) THEN
  ERT_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FSAF_ROW_POINT) THEN
  ERT_STEP(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ERT_FORCED_LEFT) THEN
  ERT_STEP(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `&1`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  ASM_MESON_TAC[]);;
