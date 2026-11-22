(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryBarCrosspoint/Main.lean     *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint).      *)
(* The full all-angle ordinary-square / foreign-bar theorem.                 *)
(* Input: obci_input (Inputs); positive: OBCP_POSITIVE; negative:           *)
(* OBCN_NEGATIVE; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME;        *)
(* S12.inside_translated_iff: WSC_INSIDE_TRANSLATED; S12.inside_segment:    *)
(* CES_INSIDE_SEGMENT.  The chart (pullX A).translated 2 2 of               *)
(* A = (c, s, u, v, a) is (--c, s, u - &2 * c - &2 * s, --v - a - &2 * s +   *)
(* &2 * c, a) with inside x y <=> A inside (2 - x) (2 + y) (OBCM_CHART).     *)
(* The bar of K is used directly as a horizontal segment (the Lean proof    *)
(* goes through WallProfile.vertical_owned of pullSwap K).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Positive.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Negative.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/WallSignChord.ml";;

(* Lean: point *)
let OBCM_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a
     ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `obci_input c1 s1 u1 v1 a1` ASSUME_TAC THENL
   [MATCH_MP_TAC OBCI_INPUT_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) then
      REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OBCP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OBCN_NEGATIVE THEN EXISTS_TAC `--s1:real` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: point_original *)
let OBCM_POINT_ORIGINAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&1543 / &500) (&1) /\
     (forall x. &113 / &50 <= x ==> x <= &72 / &25 ==> ~linside c s u v a x (&1))
     ==> linside c s u v a (&5 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`;
                `v - (--s * &2 + c * &2)`; `a:real`] OBCM_POINT) THEN
  REWRITE_TAC[obci_input; WSC_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&2 + x` o
    check (fun th -> is_forall(concl th) && is_imp(snd(strip_forall(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* the chart (pullX A).translated 2 2 *)
let OBCM_CHART = prove
 (`forall c s u v a x y.
     linside (--c) s (u - &2 * c - &2 * s) (--v - a - &2 * s + &2 * c) a x y <=>
     linside c s u v a (&2 - x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* close a goal from an ldisj assumption (unfolded) against the square with
   cosine variable cX at the point (p, q) *)
let OBCM_APART_TAC cX p q =
  FIRST_ASSUM(MP_TAC o SPECL [p; q] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) cX)) (concl th))) THEN
  (fun (asl,w as g) ->
     REWRITE_TAC(filter (fun th -> not(is_forall(concl th))) (map snd asl)) g);;

(* Lean: southwest_point_and_left_omission *)
let OBCM_SOUTHWEST_POINT_AND_LEFT_OMISSION = prove
 (`forall cA sA uA vA aA cK sK uK vK aK cL sL uL vL aL.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&1) (&87 / &50) /\
     linside cA sA uA vA aA (&1) (&8 / &5) /\
     linside cK sK uK vK aK (&28 / &25) (&1) /\
     linside cK sK uK vK aK (&87 / &50) (&1) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     ~linside cA sA uA vA aA (&457 / &500) (&1) /\
     ldisj cA sA uA vA aA cK sK uK vK aK /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&3 / &2) (&2) /\
         ~linside cL sL uL vL aL (&87 / &50) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (&3 / &2) (&2)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`--cA:real`; `sA:real`; `uA - &2 * cA - &2 * sA`;
                  `--vA - aA - &2 * sA + &2 * cA`; `aA:real`] OBCM_POINT) THEN
    REWRITE_TAC[obci_input; OBCM_CHART; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [OBCM_APART_TAC `cL:real` `&457 / &500` `&2`; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                  `&28 / &25`; `&1`; `&87 / &50`; `&1`;
                  `(&50 / &31) * ((&2 - x) - &28 / &25)`] CES_INSIDE_SEGMENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 - &50 / &31 * (&2 - x - &28 / &25)) * &28 / &25 +
      (&50 / &31 * (&2 - x - &28 / &25)) * &87 / &50 = &2 - x /\
      (&1 - &50 / &31 * (&2 - x - &28 / &25)) * &1 +
      (&50 / &31 * (&2 - x - &28 / &25)) * &1 = &1`
     (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    OBCM_APART_TAC `cK:real` `&2 - x` `&1`;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&457 / &500`; `&2`; `&87 / &50`; `&2`; `&293 / &413`]
    CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_TAC THEN OBCM_APART_TAC `cL:real` `&3 / &2` `&2`);;
