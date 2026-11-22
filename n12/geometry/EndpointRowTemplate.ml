(* ========================================================================= *)
(* Port of Compact/Geometry/EndpointRowTemplate.lean                         *)
(*                                                                           *)
(* The structures Premises / DualPremises become hypothesis lists, with      *)
(* lsquare for the OpenSquare invariants.  closed_swap (private) is          *)
(* LCLOSED_PULLSW; pullSwap q = (s, c, u, --v - a, a).                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;
needs "n12/geometry/CentralCross.ml";;

(* Lean: canonical_left (private) *)
let ERT_CANONICAL_LEFT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&87 / &50) (&2) /\ linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&5 / &2)
     ==> linside c s u v a (&1) (&12 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `u + a <= c * &2 + s * &12 / &5` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(u < c * &2 + s * &12 / &5 /\ c * &2 + s * &12 / &5 < u + a /\
                   v < --s * &2 + c * &12 / &5 /\ --s * &2 + c * &12 / &5 < v + a)` THEN
    REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &2 + s * &5 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(u < c * &2 + s * &5 / &2 /\ c * &2 + s * &5 / &2 < u + a /\
                   v < --s * &2 + c * &5 / &2 /\ --s * &2 + c * &5 / &2 < v + a)` THEN
    REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: forced_left *)
let ERT_FORCED_LEFT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&87 / &50) (&2) /\ linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&5 / &2)
     ==> linside c s u v a (&1) (&12 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  MATCH_MP_TAC ERT_CANONICAL_LEFT THEN ASM_REWRITE_TAC[]);;

(* apply a lemma instance: prove its antecedent from the assumptions, then
   add its conclusion as an assumption *)
let ERT_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

(* Lean: impossible (the structure Premises is the hypothesis list) *)
let ERT_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\
     lsquare cL sL uL vL aL /\ lsquare cR sR uR vR aR /\
     &1 < aA /\ &1 < aB /\ &1 < aR /\
     lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&87 / &50) (&2) /\
     linside cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cR sR uR vR aR (&3) (&87 / &50) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  ERT_STEP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FSLB_RIGHT_POINT) THEN
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

(* Lean: two_arms *)
let ERT_TWO_ARMS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     lclosed c s u v a (&2) (&113 / &50) /\
     lclosed c s u v a (&113 / &50) (&2) /\
     lclosed c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&12 / &5) (&3)
     ==> linside c s u v a (&2) (&5 / &2) \/ linside c s u v a (&5 / &2) (&2)`,
  REWRITE_TAC[CCR_POINT]);;

(* Lean: dual_impossible (the structure DualPremises is the hypothesis list) *)
let ERT_DUAL_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cC sC uC vC aC cL sL uL vL aL cD sD uD vD aD.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\ lsquare cC sC uC vC aC /\
     lsquare cL sL uL vL aL /\ lsquare cD sD uD vD aD /\
     &1 < aA /\ &1 < aB /\ &1 < aC /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     linside cB sB uB vB aB (&87 / &50) (&2) /\
     linside cB sB uB vB aB (&8 / &5) (&3) /\
     linside cC sC uC vC aC (&2) (&87 / &50) /\
     linside cC sC uC vC aC (&3) (&8 / &5) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     lclosed cD sD uD vD aD (&12 / &5) (&1) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cC sC uC vC aC /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cC sC uC vC aC cD sD uD vD aD
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ERT_TWO_ARMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ERT_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FSAF_ROW_POINT) THEN
    ERT_STEP(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ERT_FORCED_LEFT) THEN
    ERT_STEP(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                    `&1`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
    ASM_MESON_TAC[];
    ERT_STEP(REWRITE_RULE[LINSIDE_PULLSW; LCLOSED_PULLSW]
      (SPECL [`sA:real`; `cA:real`; `uA:real`; `--vA - aA:real`; `aA:real`] FSAF_ROW_POINT)) THEN
    ERT_STEP(REWRITE_RULE[LINSIDE_PULLSW]
      (SPECL [`sC:real`; `cC:real`; `uC:real`; `--vC - aC:real`; `aC:real`] ERT_FORCED_LEFT)) THEN
    ERT_STEP(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                    `&12 / &5`; `&1`] OUTSIDE_OF_CLOSED) THEN
    ASM_MESON_TAC[]]);;
