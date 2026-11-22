(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/ShortBarNegative.lean               *)
(* (N12Compact.C1092MMMPShortBarNegative).  A true short foreign bar excludes *)
(* the entire nonpositive inward frame.  Normal: c977cc_normal;              *)
(* short_projections: WFP_SHORT_PROJECTIONS; NearCrossing.point:             *)
(* C1092NCR_POINT; centerY: lcy.                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NearCrossing.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092SBN_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SBN_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092SBN_LIN_TAC;;

let C1092SBN_SHORT_TAC dx dy =
  MP_TAC(SPECL [`cC:real`; `sC:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: impossible *)
let C1092SBN_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cC (--sC) /\ &1 < aC /\ aC = aW /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     ~linside cC sC uC vC aC (&0) (&0) /\
     ~linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (&13 / &50) (&1) /\
     (forall x. &0 <= x ==> x <= &13 / &50 ==> ~linside cC sC uC vC aC x (&1)) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cW sW uW vW aW (&1) (&39 / &100) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t && can (find_term ((=) `uC:real`)) t) ths)) THEN
  SUBGOAL_THEN `&0 <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SBN_MISS_TAC `~linside cC sC uC vC aC (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --sC` ASSUME_TAC THENL [C1092SBN_LIN_TAC; ALL_TAC] THEN
  C1092SBN_SHORT_TAC `&7 / &10` `&7 / &10` THEN
  SUBGOAL_THEN `uC + aC <= cC + (&2 / &5) * sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SBN_MISS_TAC `~linside cC sC uC vC aC (&1) (&2 / &5)`; ALL_TAC] THEN
  C1092SBN_SHORT_TAC `&37 / &50` `--(&3 / &5)` THEN
  SUBGOAL_THEN `uC < (&13 / &50) * cC + sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN C1092SBN_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= cC - (&13 / &50) * sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SBN_MISS_TAC `~linside cC sC uC vC aC (&13 / &50) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + cC` ASSUME_TAC THENL [C1092SBN_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&13 / &50) * (&1 + cC) + sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&1 + cC`; `cC - (&13 / &50) * sC - &1`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C1092SBN_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`--sC`; `--((&13 / &50) * (&1 + cC) + sC)`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C1092SBN_LIN_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(&1 + cC) * (cC - (&13 / &50) * sC - &1) =
                  --sC * ((&13 / &50) * (&1 + cC) + sC)` ASSUME_TAC THENL
     [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092SBN_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cC:real`; `--sC`] C1092NCR_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--sC / (&1 + cC)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `&13 / &50`)) (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN C1092SBN_LIN_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN C1092SBN_LIN_TAC; ASM_REWRITE_TAC[]]);;
