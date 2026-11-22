(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareAAll.lean                              *)
(*                                                                           *)
(* Squares A = (cA,sA,uA,vA,aA), B = (cB,...), R = (cR,...).                 *)
(* InsideContainer R is lcont; disjointness is ldisj.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareRHigh.ml";;
needs "n12/geometry/FourSquareANarrow.ml";;

(* Lean: point *)
let FSAA_POINT = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ cB * cB + sB * sB = &1 /\ cR * cR + sR * sR = &1 /\
     &0 < aB /\ &1 < aA /\ &1 < aR /\
     lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&81 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> linside cA sA uA vA aA (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] FSRH_RIGHT_POINT) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN ASM_REWRITE_TAC[ldisj] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&3`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&5 / &2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th))))))) = "linside"
      with Failure _ -> false) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  MATCH_MP_TAC FSAN_POINT_OF_HIGHER_R THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then REWRITE_TAC[th] else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
