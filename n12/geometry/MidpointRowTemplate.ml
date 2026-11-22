(* ========================================================================= *)
(* Port of Compact/Geometry/MidpointRowTemplate.lean                         *)
(* The structure Premises A B L R topX becomes the hypothesis list           *)
(* (lsquare = OpenSquare invariants).  close (private) is LINSIDE_CLOSED.    *)
(* pullX q = (--c, s, u - 4c, --v - a - 4s, a).                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/MidpointSection.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;
needs "n12/geometry/EndpointRowTemplate.ml";;

let MPRT_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[LINSIDE_CLOSED] THEN NO_TAC; ASM_MESON_TAC[]]) in
  ASSUME_TAC (MP th ath) g;;

(* Lean: impossible *)
let MPRT_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR topX.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\
     lsquare cL sL uL vL aL /\ lsquare cR sR uR vR aR /\
     &1 < aA /\ &1 < aB /\ &1 < aL /\ &1 < aR /\
     lcont cB sB uB vB aB /\ lcont cL sL uL vL aL /\ lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&87 / &50) (&2) /\
     linside cB sB uB vB aB topX (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&1) (&87 / &50) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cR sR uR vR aR (&3) (&87 / &50) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  ASSUME_TAC(MATCH_MP LCONT_PULLX (ASSUME `lcont cL sL uL vL aL`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont; LINSIDE_PULLX]) THEN
  (* highR *)
  ERT_STEP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FSLB_RIGHT_POINT) THEN
  (* highL, through the reflection of L and B *)
  MPRT_STEP(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
   (REWRITE_RULE[ldisj; lcont; LINSIDE_PULLX; LCLOSED_PULLX]
    (SPECL [`--cL:real`; `sL:real`; `uL - &4 * cL:real`; `--vL - aL - &4 * sL:real`; `aL:real`;
            `--cB:real`; `sB:real`; `uB - &4 * cB:real`; `--vB - aB - &4 * sB:real`; `aB:real`]
     FSLB_RIGHT_POINT))) THEN
  (* highA *)
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
  (* the unit section of B at height 5/2 hits the grid *)
  ERT_STEP(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
            `&87 / &50`; `topX:real`; `&5 / &2`] MPS_OF_UNIT_SPAN)) THEN
  ERT_STEP(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `&5 / &2`] MPS_GRID_HIT) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2` ASSUME_TAC THENL
   [UNDISCH_TAC `j < 3` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_MESON_TAC[]);;
