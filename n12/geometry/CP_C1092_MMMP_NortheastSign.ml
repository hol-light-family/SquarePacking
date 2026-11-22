(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastSign.lean                  *)
(* (N12Compact.C1092MMMPNortheastSign).  Full central-angle cover for the    *)
(* MMMP northeast sign.  NortheastNegativeFaces.faces: C1092MNNF_FACES;      *)
(* NortheastPositiveCentral.impossible: C1092MNPC_IMPOSSIBLE;                *)
(* MMMMNegativeNeighbor.impossible_faces: C1092MNN_IMPOSSIBLE_FACES;         *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastPositiveCentral.ml";;
needs "n12/geometry/CP_C1092_MMMMNegativeNeighbor.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: nonpositive_impossible *)
let C1092MNSG_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\ c977cc_normal cB (--sB) /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (--(&39 / &100)) (--(&1)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&13 / &50) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&0) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&1) /\
     ~linside cB sB uB vB aB (--(&543 / &500)) (&0) /\
     ~linside cB sB uB vB aB (--(&1)) (&1) /\
     ~linside cB sB uB vB aB (--(&1 / &2)) (&0) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092MNNF_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mnnf_faces] o
    check (fun th -> can (term_match [] `c1092mnnf_faces c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real`
    (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aC`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
      C1092MNPC_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[ldisj; c1092mnnf_faces; c977cc_normal; REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
      C1092MNN_IMPOSSIBLE_FACES) THEN
    ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: positive *)
let C1092MNSG_POSITIVE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\ &0 < cB /\ abs sB <= cB /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (--(&39 / &100)) (--(&1)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&13 / &50) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&0) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&1) /\
     ~linside cB sB uB vB aB (--(&543 / &500)) (&0) /\
     ~linside cB sB uB vB aB (--(&1)) (&1) /\
     ~linside cB sB uB vB aB (--(&1 / &2)) (&0) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> &0 < sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092MNSG_NONPOSITIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
