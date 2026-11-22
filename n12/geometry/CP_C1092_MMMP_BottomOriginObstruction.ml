(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomOriginObstruction.lean        *)
(* (N12Compact.C1092MMMPBottomOriginObstruction).  Completed local Theorem 1 *)
(* of DOUBLE-RIGHT-BOTTOM-ORIGIN.  faceSeparation / separated / ownU:       *)
(* ABT_FOUR_AXES, ABT_OWN_TAC; PositiveInwardHalfangle: C1092MPIH_*;         *)
(* BottomBoundaryOrder.exists_frame: C1092BBO_EXISTS_FRAME;                  *)
(* BottomOwnMargin / BottomBoundaryMargin: C1092BOM_ / C1092BBM_ theorems.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_BottomOwnMargin.ml";;

(* Lean: alternatives (private) *)
let C1092BOO_ALTERNATIVES = prove
 (`forall cC sC uC vC aC cR sR uR vR aR z.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     aC = aR /\ &0 < cC /\ &0 < sC /\ &0 < cR /\ &0 < sR /\ z < &2 / &5 /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&1) z /\
     linside cR sR uR vR aR (&543 / &500) (&0) /\
     linside cR sR uR vR aR (&1) (&2 / &5) /\
     ldisj cC sC uC vC aC cR sR uR vR aR
     ==> uC + aC <= ABT_lower cR sR uR vR aR cC sC \/
         ABT_upper cC sC uC vC aC cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aR`)) THEN
  let qs = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
  and rs = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aC:real`] in
  let dirs = [`cC:real`,`sC:real`; `--sC`,`cC:real`; `cR:real`,`sR:real`; `--sR`,`cR:real`] in
  ABT_ALL_SB_TAC [qs,(`&13 / &50`,`&0`); qs,(`&1`,`z:real`);
                  rs,(`&543 / &500`,`&0`); rs,(`&1`,`&2 / &5`)] dirs THEN
  ABT_OWN_TAC qs THEN ABT_OWN_TAC rs THEN
  MP_TAC(SPECL [`cC:real`; `&2 / &5 - z`] REAL_LT_MUL) THEN
  MP_TAC(SPECL [`cR:real`; `&2 / &5 - z`] REAL_LT_MUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT DISCH_TAC THEN
  ABT_ARITH_TAC);;

(* Lean: impossible *)
let C1092BOO_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aW /\ c977cc_normal cC sC /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     ~linside cC sC uC vC aC (&0) (&0) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     ~linside cC sC uC vC aC (&1 / &2) (&1) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cW sW uW vW aW (&1) (&2 / &5) /\
     ~linside cW sW uW vW aW (&1) (&0) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cC sC uC vC aC (&1) (&13 / &50)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPIH_ENTRANCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPIH_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C1092BBO_EXISTS_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `p:real`
    (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  SUBGOAL_THEN `linside b t p q aC (&543 / &500) (&0) /\ linside b t p q aC (&1) (&2 / &5) /\
                ldisj cC sC uC vC aC b t p q aC` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ldisj] THEN RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092bbo_data] o
    check (fun th -> can (term_match [] `c1092bbo_data a b c d e f g h i j`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `b:real`; `t:real`; `p:real`; `q:real`; `aC:real`;
                `C1092WPS_half cC sC`] C1092BOO_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
      check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
    REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `b:real`; `t:real`; `p:real`; `q:real`; `aC:real`]
      C1092BOM_OWN_NORMAL_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `b:real`; `t:real`; `p:real`; `q:real`; `aC:real`]
      C1092BBM_BOUNDARY_NORMAL_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[]]);;
