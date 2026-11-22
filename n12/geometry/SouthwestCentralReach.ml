(* ========================================================================= *)
(* Port of Compact/Geometry/SouthwestCentralReach.lean (Jatloe N12).          *)
(* Strict central crosspoints from owned points, missing markers and a       *)
(* foreign singleton segment.  pullX/pullY/pullSwap: LINSIDE_PULLX/Y/SW;      *)
(* S12.inside_segment: CES_INSIDE_SEGMENT.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareANarrow.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: northeast (close is LINSIDE_CLOSED) *)
let SWCR_NORTHEAST = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&5 / &2)
     ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&2) (&5 / &2)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC FSAN_POINT_OF_HIGHER_R THEN ASM_SIMP_TAC[LINSIDE_CLOSED]);;

let SWCR_PULLXY = prove
 (`forall c s u v a x y.
     linside (--c) (--s) ((u - &4 * s) - &4 * c) (--(&4 * c - v - a) - a - &4 * --s) a x y
     <=> linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY]);;

(* Lean: below *)
let SWCR_BELOW = prove
 (`forall cA sA uA vA aA cL sL uL vL aL.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     ~linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&1) (&87 / &50) /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t ->
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `&1`; `&28 / &25`; `&1`; `&87 / &50`; t] CES_INSIDE_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC)
   [`&19 / &31`; `&24 / &31`] THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&1) (&3 / &2) /\
                ~linside cA sA uA vA aA (&1) (&8 / &5)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cL sL uL vL aL` THEN
    REWRITE_TAC[ldisj] THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`&1`; `&3 / &2`] th) THEN
                         MP_TAC(SPECL [`&1`; `&8 / &5`] th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `&2`; `&5 / &2`] SWCR_PULLXY) THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SWCR_NORTHEAST THEN
  REWRITE_TAC[SWCR_PULLXY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: left *)
let SWCR_LEFT = prove
 (`forall cA sA uA vA aA cO sO uO vO aO.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cO * cO + sO * sO = &1 /\ &0 < aO /\
     &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     ~linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     ldisj cA sA uA vA aA cO sO uO vO aO
     ==> linside cA sA uA vA aA (&3 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN
  MATCH_MP_TAC SWCR_BELOW THEN
  MAP_EVERY EXISTS_TAC [`sO:real`; `cO:real`; `uO:real`; `--vO - aO:real`; `aO:real`] THEN
  ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
  UNDISCH_TAC `ldisj cA sA uA vA aA cO sO uO vO aO` THEN
  REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN FIRST_X_ASSUM(MATCH_ACCEPT_TAC o SPECL [`y:real`; `x:real`])]);;
