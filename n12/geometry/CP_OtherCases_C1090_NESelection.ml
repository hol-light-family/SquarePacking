(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/NESelection.lean              *)
(* (namespace N12Compact.Completion.OtherCases.C1090.NESelection).          *)
(* NE-SELECTION-LEMMA.  Squares S = cS sS uS vS aS, E = cE sE uE vE aE.      *)
(* C981CompletionOutwardAnchor.nonnegative_impossible:                      *)
(* C981OA_NONNEGATIVE_IMPOSSIBLE; CommonCases.OutwardPoint.                 *)
(* positive_point_original: CCOP_POSITIVE_POINT_ORIGINAL; OutwardBarPoint.  *)
(* positive_point_original: OCOBP_POSITIVE_POINT_ORIGINAL; CommonCases.     *)
(* InwardPoint.point_original: CCIP_POINT_ORIGINAL; InwardTopPoint.         *)
(* point_original: OCITP_POINT_ORIGINAL; C1092MixedSpan.impossible:         *)
(* C1092MS_IMPOSSIBLE; pullY: LINSIDE_PULLY; canonical_frame:               *)
(* CLF_CANONICAL_FRAME.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/CP_OtherCases_InwardTopPoint.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;

(* Lean: Input (structure) *)
let occ1090nes_input = new_definition
 `occ1090nes_input (cS:real) sS uS vS aS (cE:real) sE uE vE aE <=>
    &1 < aS /\ &1 < aE /\
    ldisj cS sS uS vS aS cE sE uE vE aE /\
    linside cS sS uS vS aS (&47 / &20) (&33 / &20) /\
    linside cS sS uS vS aS (&3) (&87 / &50) /\
    linside cS sS uS vS aS (&3) (&8 / &5) /\
    ~linside cS sS uS vS aS (&3) (&1) /\
    ~linside cS sS uS vS aS (&1543 / &500) (&1) /\
    ~linside cS sS uS vS aS (&1543 / &500) (&2) /\
    (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> ~linside cS sS uS vS aS x (&1)) /\
    linside cE sE uE vE aE (&47 / &20) (&47 / &20) /\
    ~linside cE sE uE vE aE (&33 / &20) (&47 / &20) /\
    ~linside cE sE uE vE aE (&3) (&113 / &50) /\
    ~linside cE sE uE vE aE (&3) (&12 / &5) /\
    (linside cE sE uE vE aE (&2) (&113 / &50) \/ linside cE sE uE vE aE (&12 / &5) (&3)) /\
    (linside cE sE uE vE aE (&113 / &50) (&2) \/ linside cE sE uE vE aE (&113 / &50) (&3))`;;

let OCC1090NES_HYPS =
 `cS * cS + sS * sS = &1 /\ &0 < aS /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
  occ1090nes_input cS sS uS vS aS cE sE uE vE aE`;;

let OCC1090NES_UNFOLD_TAC =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match [] `occ1090nes_input a b c d e f g h i j`) (concl th))) THEN
  REWRITE_TAC[occ1090nes_input; ldisj; IMP_CONJ] THEN REPEAT DISCH_TAC;;

(* Lean: negative_frame *)
let OCC1090NES_NEGATIVE_FRAME = prove
 (`forall cS sS uS vS aS cE sE uE vE aE.
      cS * cS + sS * sS = &1 /\ &0 < aS /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      occ1090nes_input cS sS uS vS aS cE sE uE vE aE /\
      linside cE sE uE vE aE (&113 / &50) (&2)
      ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
            &0 < c' /\ s' < &0 /\ --s' <= c' /\ a' = aS /\
            (forall x y. linside c' s' u' v' a' x y <=> linside cS sS uS vS aS x y)`,
  REPEAT GEN_TAC THEN OCC1090NES_UNFOLD_TAC THEN
  MP_TAC(SPECL [`cS:real`; `sS:real`; `uS:real`; `vS:real`; `aS:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s1 < &0` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aS`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
       is_eq(snd(strip_forall(concl th))) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  MATCH_MP_TAC C981OA_NONNEGATIVE_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aS:real`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&113 / &50`; `&2`] o
      check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 && is_neg(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[]]);;

(* the reflection y -> 4 - y (Lean pullY) of the frame square *)
let OCC1090NES_PULLY = prove
 (`forall c s u v a x y. linside c (--s) (u - &4 * s) (&4 * c - v - a) a x y <=>
                   linside c s u v a x (&4 - y)`,
  REWRITE_TAC[LINSIDE_PULLY]);;

(* Lean: outward_points *)
let OCC1090NES_OUTWARD_POINTS = prove
 (`forall cS sS uS vS aS cE sE uE vE aE.
      cS * cS + sS * sS = &1 /\ &0 < aS /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      occ1090nes_input cS sS uS vS aS cE sE uE vE aE /\
      linside cE sE uE vE aE (&113 / &50) (&2)
      ==> linside cS sS uS vS aS (&123 / &50) (&201 / &100) /\
          linside cS sS uS vS aS (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCC1090NES_NEGATIVE_FRAME) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aS`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else NO_TAC) THEN
  UNDISCH_TAC `occ1090nes_input cS sS uS vS aS cE sE uE vE aE` THEN
  REWRITE_TAC[occ1090nes_input; ldisj] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
       is_eq(snd(strip_forall(concl th))) && can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
       is_eq(snd(strip_forall(concl th))) && can (find_term ((=) `linside`)) (concl th)
    then ALL_TAC else NO_TAC) THEN
  SUBGOAL_THEN `~linside c1 s1 u1 v1 aS (&113 / &50) (&2)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&113 / &50`; `&2`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        is_neg(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `--s1`; `u1 - &4 * s1`; `&4 * c1 - v1 - aS`; `aS:real`]
    CCOP_POSITIVE_POINT_ORIGINAL) THEN
  MP_TAC(SPECL [`c1:real`; `--s1`; `u1 - &4 * s1`; `&4 * c1 - v1 - aS`; `aS:real`]
    OCOBP_POSITIVE_POINT_ORIGINAL) THEN
  REWRITE_TAC[OCC1090NES_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: f7_of_g6 *)
let OCC1090NES_F7_OF_G6 = prove
 (`forall cS sS uS vS aS cE sE uE vE aE.
      cS * cS + sS * sS = &1 /\ &0 < aS /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      occ1090nes_input cS sS uS vS aS cE sE uE vE aE /\
      linside cE sE uE vE aE (&113 / &50) (&2)
      ==> linside cE sE uE vE aE (&12 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCC1090NES_OUTWARD_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[occ1090nes_input; ldisj] o
    check (fun th -> concl th = `occ1090nes_input cS sS uS vS aS cE sE uE vE aE`)) THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `linside cE sE uE vE aE (&2) (&113 / &50)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--sE`; `uE - &4 * sE`; `&4 * cE - vE - aE`; `aE:real`]
    CCIP_POINT_ORIGINAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OCC1090NES_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&47 / &20`; `&33 / &20`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[OCC1090NES_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&123 / &50`; `&201 / &100`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[]);;

(* the composite rotation pullSwap (pullX E) *)
let OCC1090NES_ROTATE = prove
 (`forall c s u v a x y. linside s (--c) (u - &4 * c) (v + &4 * s) a x y <=>
                   linside c s u v a (&4 - y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: g7 *)
let OCC1090NES_G7 = prove
 (`forall cS sS uS vS aS cE sE uE vE aE.
      cS * cS + sS * sS = &1 /\ &0 < aS /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      occ1090nes_input cS sS uS vS aS cE sE uE vE aE
      ==> linside cE sE uE vE aE (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `linside cE sE uE vE aE (&113 / &50) (&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `occ1090nes_input cS sS uS vS aS cE sE uE vE aE` THEN
    REWRITE_TAC[occ1090nes_input] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL OCC1090NES_F7_OF_G6) THEN
  MP_TAC(SPEC_ALL OCC1090NES_OUTWARD_POINTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[occ1090nes_input; ldisj] o
    check (fun th -> concl th = `occ1090nes_input cS sS uS vS aS cE sE uE vE aE`)) THEN
  ASM_CASES_TAC `linside cE sE uE vE aE (&2) (&113 / &50)` THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
      OCITP_POINT_ORIGINAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&47 / &20`; `&33 / &20`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&101 / &40`; `&17 / &8`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`sE:real`; `--cE`; `uE - &4 * cE`; `vE + &4 * sE`; `aE:real`]
      C1092MS_IMPOSSIBLE) THEN
    REWRITE_TAC[OCC1090NES_ROTATE] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: selection *)
let OCC1090NES_SELECTION = prove
 (`forall cS sS uS vS aS cE sE uE vE aE.
      cS * cS + sS * sS = &1 /\ &0 < aS /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      occ1090nes_input cS sS uS vS aS cE sE uE vE aE
      ==> linside cE sE uE vE aE (&113 / &50) (&3) /\
          (linside cE sE uE vE aE (&113 / &50) (&2) ==>
           linside cE sE uE vE aE (&12 / &5) (&3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OCC1090NES_G7 THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC OCC1090NES_F7_OF_G6 THEN ASM_MESON_TAC[]]);;
