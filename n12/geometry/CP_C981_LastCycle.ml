(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastCycle.lean                             *)
(* (N12Compact.C981CompletionLastCycle).  Complete continuous ending of the  *)
(* last two original C981 cycles.                                             *)
(* The Lean rotate q (turn^3 o pullSwap o pullY) is the explicit square       *)
(* (c, s, 4c - v - a, u - 4s, a) (C981CC_INSIDE_ROTATE, re-stated here as    *)
(* C981LC_INSIDE_ROTATE); work q = (rotate q).translated 2 2 is the explicit  *)
(* square (c, s, 2c - 2s - v - a, u - 2s - 2c, a).  rotate_c / rotate_s /     *)
(* rotate_side / work_c / work_s / work_side hold by construction.            *)
(* canonical_frame / positive_frame are CLF_CANONICAL_FRAME (via              *)
(* C981CC_FRAME_TAC) / CLF_POSITIVE_FRAME; CentralPositivePoint.point is      *)
(* C981CPP_POINT, OppositeAngle.bound is C981OPA_BOUND, LastPositivePair /    *)
(* LastNegativePair / NegativePair.impossible are C981LPP_ / C981LNP_ /       *)
(* C981NPR_IMPOSSIBLE, UpperPoint.nonpositive is C981UP_NONPOSITIVE,          *)
(* LastRightWall.angle is C981LRW_ANGLE, inside_segment is                    *)
(* CES_INSIDE_SEGMENT.  Tag C981LC_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_CommonCycle.ml";;
needs "n12/geometry/CP_C981_LastNegativePair.ml";;
needs "n12/geometry/CP_C981_LastPositivePair.ml";;
needs "n12/geometry/CP_C981_OppositeAngle.ml";;
needs "n12/geometry/CP_C981_LastRightWall.ml";;
needs "n12/geometry/CP_C981_UpperPoint.ml";;
needs "n12/geometry/CP_C981_CentralPositivePoint.ml";;
needs "n12/geometry/CP_C981_NegativePair.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: inside_rotate *)
let C981LC_INSIDE_ROTATE = prove
 (`forall c s u v a x y.
     linside c s (&4 * c - v - a) (u - &4 * s) a x y <=> linside c s u v a y (&4 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inside_work *)
let C981LC_INSIDE_WORK = prove
 (`forall c s u v a x y.
     linside c s (&2 * c - &2 * s - v - a) (u - &2 * s - &2 * c) a x y <=>
     linside c s u v a (&2 + y) (&2 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C981LC_LIN = NLIN_TAC ~deg2:false [];;

(* a segment hypothesis !t. lo <= t ==> t <= hi ==> ~P t (curried or not) *)
let C981LC_SEG_TAC =
  GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] th) THEN
    REPEAT CONJ_TAC THEN C981LC_LIN);;

(* a wall hypothesis !x y. P x y ==> y <= k from rightWall *)
let C981LC_WALL_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REAL_ARITH_TAC;;

let C981LC_DISCH =
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; C981LC_WALL_TAC; C981LC_SEG_TAC;
         C981LC_LIN; ASM_MESON_TAC[]];;

let C981LC_INST extra th =
  CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (REWRITE_RULE(extra @ [ldisj; C981LC_INSIDE_WORK; C981LC_INSIDE_ROTATE; REAL_NEG_NEG]) th);;

(* Lean: impossible *)
let C981LC_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cA sA uA vA aA cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aC /\ aC <= &1001 / &1000 /\ aC = aB /\ aC = aA /\ aB = aR /\
     (forall x y. linside cR sR uR vR aR x y ==> x <= &4) /\
     linside cC sC uC vC aC (&2) (&2) /\ linside cC sC uC vC aC (&3 / &2) (&2) /\
     linside cC sC uC vC aC (&2) (&5 / &2) /\ linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     ~linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     (forall y. &113 / &50 <= y ==> y <= &14 / &5 ==> ~linside cC sC uC vC aC (&1) y) /\
     (forall x. &36 / &25 <= x ==> x <= &2 ==> ~linside cC sC uC vC aC x (&3)) /\
     linside cB sB uB vB aB (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&113 / &50) (&3) /\ linside cB sB uB vB aB (&12 / &5) (&3) /\
     ~linside cB sB uB vB aB (&2) (&12 / &5) /\ ~linside cB sB uB vB aB (&2) (&3) /\
     ~linside cB sB uB vB aB (&3) (&12 / &5) /\ ~linside cB sB uB vB aB (&3) (&3) /\
     ~linside cB sB uB vB aB (&2) (&1543 / &500) /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\ linside cA sA uA vA aA (&113 / &50) (&2) /\
     ~linside cA sA uA vA aA (&3) (&87 / &50) /\
     (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> ~linside cA sA uA vA aA x (&1)) /\
     ~linside cC sC uC vC aC (&1) (&87 / &50) /\
     linside cR sR uR vR aR (&3) (&87 / &50) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cR sR uR vR aR (&3) (&8 / &5) /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\
     ldisj cC sC uC vC aC cA sA uA vA aA /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aR`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  C981CC_FRAME_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
                   [`cF:real`; `sF:real`; `uF:real`; `vF:real`; `aF:real`] THEN
  C981CC_FRAME_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
                   [`cG:real`; `sG:real`; `uG:real`; `vG:real`; `aG:real`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  (* positivePoint *)
  SUBGOAL_THEN `&0 <= sF ==> linside cF sF uF vF aC (&2) (&131 / &50)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC(SPECL [`cF:real`; `sF:real`; `uF:real`; `vF:real`; `aC:real`] C981CPP_POINT) THEN
    C981LC_DISCH; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sG` THENL
   [SUBGOAL_THEN `c977cc_normal cG sG` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* angle *)
    MP_TAC(C981LC_INST [] (SPECL [`cG:real`; `sG:real`; `&2 * cG - &2 * sG - vG - aC`; `uG - &2 * sG - &2 * cG`; `aC:real`;
                  `cR:real`; `sR:real`; `&2 * cR - &2 * sR - vR - aC`; `uR - &2 * sR - &2 * cR`; `aC:real`] C981LRW_ANGLE)) THEN ANTS_TAC THENL [C981LC_DISCH; DISCH_TAC] THEN
    ASM_CASES_TAC `&0 <= sF` THENL
     [SUBGOAL_THEN `c977cc_normal cF sF` ASSUME_TAC THENL
       [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) then
        ASSUME_TAC(MP th (ASSUME `&0 <= sF`)) else NO_TAC) THEN
      MP_TAC(SPECL [`cA:real`; `sA:real`; `&2 * cA - &2 * sA - vA - aC`; `uA - &2 * sA - &2 * cA`;
                    `aC:real`] CLF_POSITIVE_FRAME) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `cQ:real` (X_CHOOSE_THEN `sQ:real` (X_CHOOSE_THEN `uQ:real`
        (X_CHOOSE_THEN `vQ:real` (X_CHOOSE_THEN `aQ:real` STRIP_ASSUME_TAC))))) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aQ:real = aC`)) THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
        then ASSUME_TAC(REWRITE_RULE[C981LC_INSIDE_WORK] th) else NO_TAC) THEN
      (* small *)
      (fun th -> FIRST_ASSUM(fun eq -> if is_forall(concl eq) && is_iff(snd(strip_forall(concl eq)))
        then MP_TAC(C981LC_INST [eq] th) else NO_TAC)) (SPECL [`cF:real`; `sF:real`; `&2 * cF - &2 * sF - vF - aC`; `uF - &2 * sF - &2 * cF`; `aC:real`;
                    `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aC:real`; `sF:real`] C981OPA_BOUND) THEN
      ANTS_TAC THENL [C981LC_DISCH; DISCH_TAC] THEN
      (* diagonal *)
      SUBGOAL_THEN `forall z. &0 <= z ==> z <= &13 / &50 ==>
                        ~linside cF sF uF vF aC (&113 / &50 - z) (&2 - z)` ASSUME_TAC THENL
       [X_GEN_TAC `z:real` THEN REPEAT DISCH_TAC THEN
        MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aC:real`;
                      `&113 / &50`; `&2`; `&2`; `&87 / &50`; `&50 / &13 * z`] CES_INSIDE_SEGMENT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN C981LC_LIN; ALL_TAC] THEN
        SUBGOAL_THEN `(&1 - &50 / &13 * z) * (&113 / &50) + (&50 / &13 * z) * &2 = &113 / &50 - z /\
                      (&1 - &50 / &13 * z) * &2 + (&50 / &13 * z) * (&87 / &50) = &2 - z`
          (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(REWRITE_RULE[REAL_ARITH `&4 - (&2 + z) = &2 - z`] (C981LC_INST []
        (SPECL [`cF:real`; `sF:real`; `&4 * cF - vF - aC`; `uF - &4 * sF`; `aC:real`;
                `cG:real`; `sG:real`; `&4 * cG - vG - aC`; `uG - &4 * sG`; `aC:real`; `sF:real`]
               C981LPP_IMPOSSIBLE))) THEN
      TRY(MATCH_MP_TAC(TAUT `p ==> ~p ==> false`)) THEN C981LC_DISCH;
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      SUBGOAL_THEN `c977cc_normal cF (--sF)` ASSUME_TAC THENL
       [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C981LC_LIN; ALL_TAC] THEN
      MP_TAC(C981LC_INST [] (SPECL [`cF:real`; `sF:real`; `&4 * cF - vF - aC`; `uF - &4 * sF`; `aC:real`;
                    `cG:real`; `sG:real`; `&4 * cG - vG - aC`; `uG - &4 * sG`; `aC:real`; `--sF:real`] C981LNP_IMPOSSIBLE)) THEN TRY(MATCH_MP_TAC(TAUT `p ==> ~p ==> false`)) THEN C981LC_DISCH];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    ASM_CASES_TAC `&0 <= sF` THENL
     [FIRST_X_ASSUM(fun th -> if is_imp(concl th) then
        ASSUME_TAC(MP th (ASSUME `&0 <= sF`)) else NO_TAC) THEN
      MP_TAC(SPECL [`cG:real`; `sG:real`; `uG:real`; `vG:real`; `aC:real`] C981UP_NONPOSITIVE) THEN
      ANTS_TAC THENL [C981LC_DISCH; DISCH_TAC] THEN ASM_MESON_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      SUBGOAL_THEN `c977cc_normal cF (--sF) /\ c977cc_normal cG (--sG)` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C981LC_LIN; ALL_TAC] THEN
      MP_TAC(C981LC_INST [] (SPECL [`cF:real`; `sF:real`; `&4 * cF - vF - aC`; `uF - &4 * sF`; `aC:real`;
                    `cG:real`; `sG:real`; `&4 * cG - vG - aC`; `uG - &4 * sG`; `aC:real`;
                    `--sF:real`; `--sG:real`] C981NPR_IMPOSSIBLE)) THEN TRY(MATCH_MP_TAC(TAUT `p ==> ~p ==> false`)) THEN C981LC_DISCH]]);;
