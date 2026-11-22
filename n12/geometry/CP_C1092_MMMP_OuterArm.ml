(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/OuterArm.lean                       *)
(* (N12Compact.C1092MMMPOuterArm).  A centered inward square cannot also own *)
(* the outer .4 point of the genuine wall neighbor.  Normal: c977cc_normal;  *)
(* OuterArmSupport.impossible: C1092OASP_IMPOSSIBLE; short_projections:      *)
(* WFP_SHORT_PROJECTIONS; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_OuterArmSupport.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092OARM_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092OARM_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

let C1092OARM_EXPAND_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t) ths));;

let C1092OARM_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092OARM_LIN_TAC;;

(* Lean: positive (private) *)
let C1092OARM_POSITIVE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cC sC /\ &1 < aC /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092OARM_NORMAL_TAC THEN
  SUBGOAL_THEN `~linside cC sC uC vC aC (&1) (&13 / &50)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  C1092OARM_EXPAND_TAC THEN
  SUBGOAL_THEN `--sC + (&13 / &50) * cC <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092OARM_MISS_TAC `~linside cC sC uC vC aC (&1) (&13 / &50)`; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= cC - (&2 / &5) * sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092OARM_MISS_TAC `~linside cC sC uC vC aC (&2 / &5) (&1)`; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `&37 / &50`; `&3 / &5`] WFP_SHORT_PROJECTIONS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN C1092OARM_LIN_TAC);;

(* Lean: negative (private) *)
let C1092OARM_NEGATIVE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cC (--sC) /\ sC < &0 /\ &1 < aC /\ aC = aW /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092OARM_NORMAL_TAC THEN
  C1092OARM_EXPAND_TAC THEN
  SUBGOAL_THEN `--(&7 / &20) * (cC - sC) <= uC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092OARM_MISS_TAC `~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &20) * (cC + sC) <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092OARM_MISS_TAC `~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20))`; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cC:real`; `--sC`] C1092OASP_IMPOSSIBLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT CONJ_TAC THEN C1092OARM_LIN_TAC;
    REWRITE_TAC[]]);;

(* Lean: impossible *)
let C1092OARM_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aW /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real`
    (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aC`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] C1092OARM_POSITIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC; REWRITE_TAC[]];
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] C1092OARM_NEGATIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC; REWRITE_TAC[]]]);;
