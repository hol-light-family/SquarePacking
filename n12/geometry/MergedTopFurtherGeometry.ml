(* ========================================================================= *)
(* Port of Compact/Cases/MergedTopFurther/Geometry.lean                      *)
(* (N12Compact.MergedTopFurther.Geometry).  Reuse of the merged-top argument *)
(* with the foreign right-hand row supplied by a singleton's vertical       *)
(* segment.  (S12.Convex.inside_segment is replaced by direct arithmetic.)  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849Positive.ml";;
needs "n12/geometry/C849Negative.ml";;

(* Lean: right_points *)
let MTFG_RIGHT_POINTS = prove
 (`forall c s u v a.
     linside c s u v a (&3) (&113 / &50) /\ linside c s u v a (&3) (&72 / &25)
     ==> linside c s u v a (&3) (&12 / &5) /\ linside c s u v a (&3) (&5 / &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: a_high *)
let MTFG_A_HIGH = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&3) (&113 / &50) /\
     linside cR sR uR vR aR (&3) (&72 / &25) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> linside cA sA uA vA aA (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] MTFG_RIGHT_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM ldisj] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`]
    FSAN_POINT_OF_HIGHER_R) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&3`; `&12 / &5`] o
    check (fun th -> can (find_term ((=) `cR:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&3`; `&5 / &2`] o
    check (fun th -> can (find_term ((=) `cR:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  C849SHAB_LIN_TAC);;

(* Lean: positive_impossible *)
let MTFG_POSITIVE_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cC sC uC vC aC cE sE uE vE aE.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     aA = aB /\ &1 < aB /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&2) (&5 / &2) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     linside cC sC uC vC aC (&113 / &50) (&3) /\
     linside cE sE uE vE aE (&1) (&3) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cB sB uB vB aB cC sC uC vC aC /\
     ldisj cB sB uB vB aB cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849PA_B_LOWER_FACE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    DISCH_TAC THEN UNDISCH_TAC `ldisj cA sA uA vA aB cB sB uB vB aB` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&5 / &2`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&3 * cB <= &7 * sB` ASSUME_TAC THENL
   [UNDISCH_TAC `lclosed cB sB uB vB aB (&33 / &20) (&47 / &20)` THEN
    REWRITE_TAC[lclosed] THEN UNDISCH_TAC `-- &2 * sB + &5 / &2 * cB <= vB` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ldisj]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    PBLR_UPPER_LEFT_MARKER_MODES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY C849SHAB_LIN_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `ldisj cB sB uB vB aB cE sE uE vE aE` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&1`; `&3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C849P_RIGHT_CAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`] C849P_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C849SHAB_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849SHAB_IN_FRAME);
    MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849SAB_IN_FRAME)] THEN
  ASM_REWRITE_TAC[ldisj] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[]);;
