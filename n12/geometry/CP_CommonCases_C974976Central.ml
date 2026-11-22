(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C974976Central.lean                *)
(* (N12Compact.CommonCases.C974976Central).  Shared continuous C974/C976     *)
(* central reduction.  Squares S = cS sS uS vS aS, N = cN sN uN vN aN        *)
(* (T = cT sT uT vT aT in top_pair).  The structure Input (extending         *)
(* C1090.NESelection.Input = occ1090nes_input) is cc974c_input, EndingInput  *)
(* is cc974c_ending.  ElbowPoint.points_original = OCEP_POINTS_ORIGINAL,      *)
(* OutwardBarPoint.point_original = OCOBP_POINT_ORIGINAL, Faces =            *)
(* ocobp_faces, OutwardBarFrame.frame_original = OCOBF_FRAME_ORIGINAL,        *)
(* CrossedElbow.impossible_original = OCCE_IMPOSSIBLE_ORIGINAL, OutwardPair.  *)
(* impossible = OCOP_IMPOSSIBLE, SharpPointScalars.half_upper/half_lower =   *)
(* OCSPS_HALF_UPPER/LOWER, UpperBarPoint.point_original =                    *)
(* OCUBP_POINT_ORIGINAL, translated = OCCE_INSIDE_TRANSLATED, pullX/pullY/   *)
(* pullSwap = LINSIDE_PULLX/Y/SW.  Tag CC974C_.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1090_NESelection.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPair.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;

let CC974C_S = [`cS:real`; `sS:real`; `uS:real`; `vS:real`; `aS:real`];;
let CC974C_N = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`];;
let cc974c_pull tms q =
  match q with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "cc974c_pull";;
let cc974c_pullx = cc974c_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let cc974c_pully = cc974c_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let cc974c_pullsw = cc974c_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* side conditions: assumptions, unit normals of pulled squares, side bounds *)
let CC974C_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
         (FIRST_ASSUM ACCEPT_TAC ORELSE (ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC));
         RASM_ARITH_TAC];;

(* add the conclusion of a lemma instance (antecedents from the assumptions) *)
let CC974C_HAVE th tup =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tup th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  MP_TAC th' THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN CC974C_SIDE_TAC; DISCH_TAC];;

(* Lean: southeast_g8 *)
let CC974C_SOUTHEAST_G8 = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aS /\
     linside cS sS uS vS aS (&47 / &20) (&33 / &20) /\
     linside cS sS uS vS aS (&3) (&87 / &50) /\
     (linside cS sS uS vS aS (&113 / &50) (&2) \/ linside cS sS uS vS aS (&3) (&8 / &5)) /\
     linside cN sN uN vN aN (&47 / &20) (&47 / &20) /\
     ldisj cS sS uS vS aS cN sN uN vN aN /\
     ~linside cS sS uS vS aS (&2) (&3 / &2) /\
     ~linside cS sS uS vS aS (&1543 / &500) (&2)
     ==> linside cS sS uS vS aS (&3) (&8 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; ldisj] THEN REPEAT DISCH_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `linside cS sS uS vS aS (&113 / &50) (&2) /\
                ~linside cS sS uS vS aS (&47 / &20) (&47 / &20)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CC974C_HAVE OCEP_POINTS_ORIGINAL CC974C_S THEN ASM_MESON_TAC[]);;

(* Lean: Input (structure, extends C1090.NESelection.Input) *)
let cc974c_input = new_definition
 `cc974c_input (cS:real) sS uS vS aS (cN:real) sN uN vN aN <=>
    occ1090nes_input cS sS uS vS aS cN sN uN vN aN /\ aS = aN /\
    ~linside cS sS uS vS aS (&2) (&3 / &2) /\
    ~linside cN sN uN vN aN (&2) (&1543 / &500)`;;

(* Lean: EndingInput (structure, extends Input) *)
let cc974c_ending = new_definition
 `cc974c_ending (cS:real) sS uS vS aS (cN:real) sN uN vN aN <=>
    cc974c_input cS sS uS vS aS cN sN uN vN aN /\
    ~linside cN sN uN vN aN (&2) (&3) /\
    ~linside cN sN uN vN aN (&3) (&3) /\
    (forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> ~linside cN sN uN vN aN (&3) y)`;;

(* unfold an Input / EndingInput assumption (fields as assumptions, the NESelection input kept) *)
let CC974C_UNFOLD_TAC =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `cc974c_ending a b c d e f g h i j`) (concl th) ||
       can (term_match [] `cc974c_input a b c d e f g h i j`) (concl th)
    then MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[cc974c_ending; cc974c_input] th))
    else NO_TAC)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `occ1090nes_input a b c d e f g h i j`) (concl th)
    then MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[occ1090nes_input; ldisj] th))
    else NO_TAC);;

let CC974C_HYPS = `cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN`;;

(* Lean: northeast_g7 *)
let CC974C_NORTHEAST_G7 = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_input cS sS uS vS aS cN sN uN vN aN
     ==> linside cN sN uN vN aN (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN CC974C_UNFOLD_TAC THEN
  CC974C_HAVE OCC1090NES_G7 (CC974C_S @ CC974C_N) THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: outward_sharp *)
let CC974C_OUTWARD_SHARP = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_input cS sS uS vS aS cN sN uN vN aN /\
     ~linside cS sS uS vS aS (&113 / &50) (&2)
     ==> linside cS sS uS vS aS (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN CC974C_UNFOLD_TAC THEN
  CC974C_HAVE OCOBP_POINT_ORIGINAL (cc974c_pully CC974C_S) THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: northeast_f7 *)
let CC974C_NORTHEAST_F7 = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_input cS sS uS vS aS cN sN uN vN aN
     ==> linside cN sN uN vN aN (&12 / &5) (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL CC974C_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL CC974C_OUTWARD_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC o rev) THEN
  UNDISCH_TAC `cc974c_input cS sS uS vS aS cN sN uN vN aN` THEN CC974C_UNFOLD_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&2) (&113 / &50)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CC974C_HAVE OCEP_POINTS_ORIGINAL (cc974c_pullsw (cc974c_pullx CC974C_N)) THEN
  ASM_CASES_TAC `linside cS sS uS vS aS (&113 / &50) (&2)` THENL
   [MATCH_MP_TAC(NOT_ELIM (CONV_RULE REAL_RAT_REDUCE_CONV
      (SPECL (CC974C_S @ [`&4 / &5`]) OCCE_IMPOSSIBLE_ORIGINAL))) THEN
    REPEAT CONJ_TAC THEN TRY CC974C_SIDE_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&14 / &5` o check (fun th ->
      can (term_match [] `forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> ~linside cS sS uS vS aS x (&1)`) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* Lean: top_pair *)
let CC974C_TOP_PAIR = prove
 (`forall cS sS uS vS aS cN sN uN vN aN cT sT uT vT aT.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     cc974c_input cS sS uS vS aS cN sN uN vN aN /\
     ldisj cN sN uN vN aN cT sT uT vT aT /\
     (linside cT sT uT vT aT (&113 / &50) (&3) \/
      (linside cT sT uT vT aT (&8 / &5) (&3) /\ linside cT sT uT vT aT (&87 / &50) (&3)))
     ==> linside cT sT uT vT aT (&8 / &5) (&3) /\ linside cT sT uT vT aT (&87 / &50) (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL CC974C_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&113 / &50`; `&3`] o REWRITE_RULE[ldisj] o check (fun th ->
    can (term_match [] `ldisj cN sN uN vN aN cT sT uT vT aT`) (concl th))) THEN
  ASM_MESON_TAC[]);;

(* Lean: outward_frame *)
let CC974C_OUTWARD_FRAME = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_input cS sS uS vS aS cN sN uN vN aN /\
     ~linside cS sS uS vS aS (&113 / &50) (&2)
     ==> exists c s u v a. c * c + s * s = &1 /\ &0 < a /\
           &0 < c /\ &0 <= s /\ s <= c /\ a = aS /\
           (forall x y. linside c s u v a x y <=>
                  linside cS (--sS) (uS - &4 * sS) (&4 * cS - vS - aS) aS x y) /\
           ocobp_faces c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a`,
  REPEAT GEN_TAC THEN CC974C_UNFOLD_TAC THEN
  MP_TAC(SPECL (cc974c_pully CC974C_S) OCOBF_FRAME_ORIGINAL) THEN
  REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN CC974C_SIDE_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM LINSIDE_PULLY]);;

(* Lean: outward_mixed_impossible *)
let CC974C_OUTWARD_MIXED_IMPOSSIBLE = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_ending cS sS uS vS aS cN sN uN vN aN /\
     ~linside cS sS uS vS aS (&113 / &50) (&2) /\
     linside cN sN uN vN aN (&2) (&113 / &50)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cc974c_input cS sS uS vS aS cN sN uN vN aN` ASSUME_TAC THENL
   [ASM_MESON_TAC[cc974c_ending]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL CC974C_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL CC974C_OUTWARD_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL CC974C_OUTWARD_FRAME) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` MP_TAC))))) THEN
  REWRITE_TAC[ocobp_faces] THEN STRIP_TAC THEN
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC o rev) THEN
  UNDISCH_TAC `cc974c_ending cS sS uS vS aS cN sN uN vN aN` THEN CC974C_UNFOLD_TAC THEN
  (* halfLow, halfHigh *)
  SUBGOAL_THEN `cr pow 2 + sr pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&13 / &87 < C1092WPS_half cr sr` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun riff ->
    if can (term_match [] `forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y`) (concl riff) then
      MATCH_MP_TAC (NOT_ELIM (CONV_RULE (REWRITE_CONV[ldisj; OCCE_INSIDE_TRANSLATED; LINSIDE_PULLY; riff;
                                             REAL_SUB_SUB2] THENC REAL_RAT_REDUCE_CONV)
        (SPECL [`cr:real`; `--sr`; `(ur - &4 * sr) - (cr * &2 + --sr * &2)`;
                `(&4 * cr - vr - ar) - (--(--sr) * &2 + cr * &2)`; `ar:real`;
                `cN:real`; `sN:real`; `uN - (cN * &2 + sN * &2)`; `vN - (--sN * &2 + cN * &2)`;
                `aN:real`; `sr:real`] OCOP_IMPOSSIBLE)))
    else NO_TAC) THEN
  REPEAT CONJ_TAC THEN
  FIRST [CC974C_SIDE_TAC;
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

(* Lean: southeast_g6 *)
let CC974C_SOUTHEAST_G6 = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_ending cS sS uS vS aS cN sN uN vN aN
     ==> linside cS sS uS vS aS (&113 / &50) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  ASM_CASES_TAC `linside cN sN uN vN aN (&2) (&113 / &50)` THENL
   [MP_TAC(SPEC_ALL CC974C_OUTWARD_MIXED_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cc974c_input cS sS uS vS aS cN sN uN vN aN` ASSUME_TAC THENL
   [ASM_MESON_TAC[cc974c_ending]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL CC974C_OUTWARD_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC o rev) THEN
  UNDISCH_TAC `cc974c_ending cS sS uS vS aS cN sN uN vN aN` THEN CC974C_UNFOLD_TAC THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&12 / &5) (&3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CC974C_HAVE OCUBP_POINT_ORIGINAL CC974C_N THEN ASM_MESON_TAC[]);;
