(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/Main.lean     *)
(* (namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint).      *)
(* C974-C976-SW-SUPPORT-POINT, Theorem 1.  Squares are c s u v a with        *)
(* c * c + s * s = &1 and &0 < a.  Input is ocswsp_input; canonical_frame is *)
(* CLF_CANONICAL_FRAME; positive / negative are OCSWSPPOS_POSITIVE /         *)
(* OCSWSPNEG_NEGATIVE; SegmentSupport.positive / negative are               *)
(* OCSWSPSS_POSITIVE / OCSWSPSS_NEGATIVE; inside_segment is                 *)
(* CES_INSIDE_SEGMENT (OO_HORIZONTAL_SEGMENT for the bottom bar).  The      *)
(* translated square of  point  is (c, s, u - 2(c+s), v - 2(c-s), a).       *)
(* Tag OCSWSPM_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Positive.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Negative.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_SegmentSupport.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: point_centered *)
let OCSWSPM_POINT_CENTERED = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a
     ==> linside c s u v a (--(&73 / &100)) (--(&1 / &25))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `ocswsp_input c' s' u' v' a'` ASSUME_TAC THENL
   [MATCH_MP_TAC OCSWSP_INPUT_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [SUBGOAL_THEN `s' <= c'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCSWSPPOS_POSITIVE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OCSWSPSS_POSITIVE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `--s' <= c' /\ &0 <= --s'` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCSWSPNEG_NEGATIVE THEN EXISTS_TAC `--s':real` THEN ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
    MATCH_MP_TAC OCSWSPSS_NEGATIVE THEN EXISTS_TAC `--s':real` THEN ASM_REWRITE_TAC[REAL_NEG_NEG]]);;

let OCSWSPM_TRANSLATE = prove
 (`forall c s u v a x y. linside c s (u - &2 * (c + s)) (v - &2 * (c - s)) a x y <=>
                   linside c s u v a (x + &2) (y + &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point *)
let OCSWSPM_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&3 / &2) (&2) /\ linside c s u v a (&2) (&3 / &2) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&2) (&1) /\
     ~linside c s u v a (&1) (&8 / &5) /\ ~linside c s u v a (&1) (&87 / &50) /\
     (forall x. &3 / &2 <= x ==> x <= &87 / &50 ==> ~linside c s u v a x (&1)) /\
     (forall t. &0 <= t ==> t <= &1 ==>
          ~linside c s u v a (&47 / &20 - &9 / &100 * t) (&33 / &20 + &7 / &20 * t))
     ==> linside c s u v a (&127 / &100) (&49 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall x. --(&1 / &2) <= x ==> x <= --(&13 / &50)
                    ==> ~linside c s u v a (x + &2) (--(&1) + &2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `--(&1) + &2 = &1`] THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x + &2` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `&87 / &50`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall t. &0 <= t ==> t <= &1 ==>
       ~linside c s u v a ((&7 / &20 - &9 / &100 * t) + &2) ((--(&7 / &20) + &7 / &20 * t) + &2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `(&7 / &20 - &9 / &100 * t) + &2 = &47 / &20 - &9 / &100 * t`;
                REAL_ARITH `(--(&7 / &20) + &7 / &20 * t) + &2 = &33 / &20 + &7 / &20 * t`] THEN
    FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&9 / &100`)) (concl th)
      then ACCEPT_TAC (SPEC `t:real` th) else NO_TAC);
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - &2 * (c + s)`; `v - &2 * (c - s)`; `a:real`]
    OCSWSPM_POINT_CENTERED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ocswsp_input; OCSWSPM_TRANSLATE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[OCSWSPM_TRANSLATE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

(* Lean: point_of_neighbours *)
let OCSWSPM_POINT_OF_NEIGHBOURS = prove
 (`forall cA sA uA vA aA cB sB uB vB (aB:real) cR sR uR vR (aR:real).
     cA * cA + sA * sA = &1 /\ &0 < aA /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\ linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\ linside cA sA uA vA aA (&2) (&3 / &2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&2) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\ ~linside cA sA uA vA aA (&1) (&87 / &50) /\
     linside cB sB uB vB aB (&3 / &2) (&1) /\ linside cB sB uB vB aB (&87 / &50) (&1) /\
     linside cR sR uR vR aR (&47 / &20) (&33 / &20) /\ linside cR sR uR vR aR (&113 / &50) (&2) /\
     (forall x y. ~(linside cA sA uA vA aA x y /\ linside cB sB uB vB aB x y)) /\
     (forall x y. ~(linside cA sA uA vA aA x y /\ linside cR sR uR vR aR x y))
     ==> linside cA sA uA vA aA (&127 / &100) (&49 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OCSWSPM_POINT THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `linside cB sB uB vB aB x (&1)` MP_TAC THENL
     [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`&3 / &2`; `&87 / &50`] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_MESON_TAC[]];
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `&47 / &20`; `&33 / &20`;
                  `&113 / &50`; `&2`; `t:real`] CES_INSIDE_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - t) * (&47 / &20) + t * (&113 / &50) = &47 / &20 - &9 / &100 * t`;
                REAL_ARITH `(&1 - t) * (&33 / &20) + t * &2 = &33 / &20 + &7 / &20 * t`] THEN
    ASM_MESON_TAC[]]);;
