(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/ResidualTopG4.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1091.Residual).             *)
(* C1091-complete-proof sections 4-7: top G4 forces both northwest inner     *)
(* points; the merged-marker seed advances the actual left wall; the        *)
(* last-cycle theorem consumes these points after one transpose.            *)
(* q : Fin 12 -> OpenSquare is  qc qs qu qv qa : num -> real  (see           *)
(* CP_OtherCases_C1091_ResidualInput.ml); unit_normal is the separate        *)
(* hypothesis  !i. i < 12 ==> qc i * qc i + qs i * qs i = &1.                *)
(* C1092MixedSpan.impossible: C1092MS_IMPOSSIBLE; MergedMarkerSeed.wall_bar *)
(* (instance q 4, q 0, q 7, q 8): C1091MMSW_ORIGINAL_OWNER_BAR;              *)
(* C981CompletionLastCycle.impossible: C981LC_IMPOSSIBLE.  The pullSwap /    *)
(* side-goal tactics are those of CP_OtherCases_C1091_ResidualNoTopG4.ml.    *)
(* Tag C1091RT_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualInput.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualNoTopG4.ml";;
needs "n12/geometry/CP_C981_LastCycle.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_OtherCases_C1091_MergedMarkerSeedWall.ml";;

(* an apartness field  !x y. ~(q i x y /\ q j x y)  of the input *)
let C1091RT_APART_TAC =
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `~(i:num = j)`)) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV;;

let C1091RT_SAME_TAC =
  FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (term_match [] `forall i j. i < 12 /\ j < 12 ==> (qa:num->real) i = qa j`) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV;;

(* Lean: northwest_points *)
let C1091RT_NORTHWEST_POINTS = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1091ri_input qc qs qu qv qa /\
     linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) /\
         linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2)` ASSUME_TAC THENL
   [C1091RN_UNFOLD_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`;
                  `7`; `11`; `&87 / &50`; `&3`] C1091RI_FOREIGN) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C1091RN_SQUARE_TAC 7 THEN C1091RN_UNFOLD_TAC THEN
  C1091RN_APPLY_TAC C1092MS_IMPOSSIBLE (c1091rn_pullsw (c1091rn_q 7)) [11; 8]);;

(* Lean: left_long_bar *)
let C1091RT_LEFT_LONG_BAR = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1091ri_input qc qs qu qv qa /\
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2)
     ==> forall y. &113 / &50 <= y ==> y <= &14 / &5
             ==> linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (c1091rn_q 4 @ c1091rn_q 0 @ c1091rn_q 7 @ c1091rn_q 8)
    C1091MMSW_ORIGINAL_OWNER_BAR) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  C1091RN_SQUARE_TAC 4 THEN C1091RN_SQUARE_TAC 0 THEN C1091RN_SQUARE_TAC 7 THEN
  C1091RN_SQUARE_TAC 8 THEN C1091RN_UNFOLD_TAC THEN
  ASM_REWRITE_TAC[lsquare; c1091mmsw_wall_input; ldisj] THEN
  REPEAT CONJ_TAC THEN C1091RT_APART_TAC);;

(* Lean: top_g4_impossible *)
let C1091RT_TOP_G4_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1091ri_input qc qs qu qv qa /\
     linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1091RT_NORTHWEST_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1091RT_LEFT_LONG_BAR) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPEC_ALL C1091RI_SOUTHEAST_CUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1091RN_SQUARE_TAC 5 THEN C1091RN_SQUARE_TAC 6 THEN C1091RN_SQUARE_TAC 7 THEN
  C1091RN_SQUARE_TAC 11 THEN C1091RN_UNFOLD_TAC THEN
  SUBGOAL_THEN `linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `&36 / &25`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(qa:num->real) 5 = qa 6 /\ qa 5 = qa 7 /\ qa 6 = qa 11` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1091RT_SAME_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(qa:num->real) 5 <= &1001 / &1000` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `&1001 / &1000`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `forall x y. linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) y x ==> x <= &4`
    ASSUME_TAC THENL
   [UNDISCH_TAC `lcont (qc 11) (qs 11) (qu 11) (qv 11) (qa 11)` THEN
    REWRITE_TAC[lcont] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun (i, j) ->
    let tm = subst [mk_small_numeral i, `i:num`; mk_small_numeral j, `j:num`]
      `forall x y. ~(linside ((qc:num->real) i) (qs i) (qu i) (qv i) (qa i) x y /\
               linside ((qc:num->real) j) (qs j) (qu j) (qv j) (qa j) x y)` in
    SUBGOAL_THEN tm ASSUME_TAC THENL [C1091RT_APART_TAC; ALL_TAC])
    [5, 6; 5, 7; 6, 11] THEN
  C1091RN_APPLY_TAC C981LC_IMPOSSIBLE
    (c1091rn_pullsw (c1091rn_q 5) @ c1091rn_pullsw (c1091rn_q 6) @
     c1091rn_pullsw (c1091rn_q 7) @ c1091rn_pullsw (c1091rn_q 11))
    [4; 9; 10; 5; 11; 2; 8; 0; 7]);;
