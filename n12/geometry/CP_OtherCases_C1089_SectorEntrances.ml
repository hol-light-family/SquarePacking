(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/SectorEntrances.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1089.SectorEntrances).       *)
(* The remaining ordinary pairs in C1089's three incoming sectors.           *)
(* Conventions of OriginalData.ml / WallCore.ml: owners p i is the owner at  *)
(* the literal mask EL i c1089sc_masks (4 -> 256, 5 -> 512, 6 -> 1024,       *)
(* 7 -> 2048, 8 -> 4096, 10 -> 16384, 11 -> 32768); for                     *)
(* MMMPSingletonEnding.impossible the family q is c1089od_owners and the     *)
(* structure Input is oc1089mse_input (the Lean import LastSectorRawEnding  *)
(* is unused).  C1092CornerTwoGaps / C1092MixedSpan .impossible =            *)
(* C1092CTG_ / C1092MS_IMPOSSIBLE.  (Lean header: "Source only,              *)
(* uncompiled".)  Tag C1089SE_.                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_OriginalData.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallCore.ml";;
needs "n12/geometry/CP_OtherCases_C1089_MMMPSingletonEnding.ml";;

let C1089SE_V = C1089WC_V;;
let c1089se_own = c1089wc_own;;
let c1089se_le x y = mk_binop `(<=):real->real->bool` x y;;
let c1089se_cover th = MP (SPEC_ALL (c1089wc_lit th)) (c1089wc_hh ());;
let C1089SE_HAVE_TAC tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;
let C1089SE_CLOSE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC; C1089WC_CLASH_TAC;
         FIRST_ASSUM(fun th -> if is_neg (concl th) then
           FIRST_ASSUM(fun th2 -> CONTR_TAC (MP (NOT_ELIM th) th2)) else NO_TAC)];;
let C1089SE_COVER_TAC th =
  MP_TAC (c1089se_cover th) THEN STRIP_TAC THEN C1089SE_CLOSE_TAC;;
let C1089SE_AT_TAC th t =
  MP_TAC (SPECL (C1089SE_V @ [t]) th) THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* Lean: clockwise_pair *)
let C1089SE_CLOCKWISE_PAIR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&12 / &5) (&3) /\
     (linside c s u v a (&113 / &50) (&2) \/ linside c s u v a (&113 / &50) (&3) \/
      linside c s u v a (&3) (&12 / &5)) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&3) (&239 / &100) /\
     ~linside c s u v a (&3) (&3)
     ==> linside c s u v a (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  let q = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  let i1 = c1089wc_inst C1092CTG_IMPOSSIBLE (q @ [`&13 / &50`; `&39 / &100`])
  and i2 = c1089wc_inst C1092MS_IMPOSSIBLE (c1089wc_sw (c1089wc_px q)) in
  SUBGOAL_THEN `s * s + c * c = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC i1 THEN MP_TAC i2 THEN ASM_REWRITE_TAC[] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC TAUT);;

let c1089se_frame_tac ms =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC ms;;

(* Lean: mmmp_ne_pair *)
let C1089SE_MMMP_NE_PAIR = prove
 (c1089wc_stmt []
    [c1089se_le `&2` (c1089wc_lcy 4096); c1089se_le `&2` (c1089wc_lcy 16384);
     c1089se_le (c1089wc_lcx 32768) `&2`]
    (mk_conj(c1089se_own 1024 `&12 / &5` `&3`, c1089se_own 1024 `&113 / &50` `&3`)),
  c1089se_frame_tac [1024] THEN
  C1089WC_USE_TAC C1089SE_V C1089WC_NORTHWEST_INWARD THEN
  C1089SE_AT_TAC C1089WC_RIGHT_HIGH `&113 / &50` THEN
  C1089SE_AT_TAC C1089WC_RIGHT_HIGH `&239 / &100` THEN
  C1089SE_HAVE_TAC (c1089se_own 1024 `&12 / &5` `&3`)
    (C1089SE_COVER_TAC C1089AC_NORTHEAST_F_COVER) THEN
  ASSUME_TAC (c1089se_cover C1089AC_NORTHEAST_G_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  C1089WC_APPLY_TAC (SPECL (c1089wc_tuple 1024) C1089SE_CLOCKWISE_PAIR));;

(* Lean: mmmp_impossible *)
let C1089SE_MMMP_IMPOSSIBLE = prove
 (c1089wc_stmt []
    [c1089se_le `&2` (c1089wc_lcy 4096); c1089se_le `&2` (c1089wc_lcy 16384);
     c1089se_le (c1089wc_lcx 32768) `&2`] `false`,
  c1089se_frame_tac [] THEN
  C1089WC_USE_TAC C1089SE_V C1089WC_NORTHWEST_INWARD THEN
  C1089WC_USE_TAC C1089SE_V C1089SE_MMMP_NE_PAIR THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089DD_TOP_COMPONENT))) THEN
  STRIP_TAC THENL [C1089WC_CLASH_TAC; ALL_TAC] THEN
  ASSUME_TAC (MP (SPEC_ALL C1089SC_ABSENT_MARKER) (c1089wc_hh ())) THEN
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[c1089od_frame]
           (MP (SPEC_ALL C1089OD_FRAME) (c1089wc_hh ())))) THEN
  DISCH_THEN(fun fr ->
    let c1089se_fside = CONJUNCT1 fr
    and c1089se_fapart = find (fun th -> can (find_term ((=) `~(i:num = j)`)) (concl th)) (CONJUNCTS fr) in
    let unit_tm = mk_forall(`i:num`, mk_imp(`i < 12`,
       mk_eq(mk_binop `(+):real->real->real`
               (mk_binop `(*):real->real->real` (mk_comb(el 0 c1089od_owners, `i:num`)) (mk_comb(el 0 c1089od_owners, `i:num`)))
               (mk_binop `(*):real->real->real` (mk_comb(el 1 c1089od_owners, `i:num`)) (mk_comb(el 1 c1089od_owners, `i:num`))),
             `&1`))) in
    SUBGOAL_THEN unit_tm ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC OO_UNIT THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC (SPECL c1089od_owners OC1089MSE_IMPOSSIBLE) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[oc1089mse_input] THEN BETA_TAC THEN REPEAT CONJ_TAC THEN
    FIRST [ACCEPT_TAC c1089se_fside; ACCEPT_TAC c1089se_fapart; ALL_TAC] THEN
    CONV_TAC C1089OD_EL_CONV THEN
    FIRST [C1089SE_CLOSE_TAC;
           MATCH_MP_TAC OO_BOX THEN FIRST_ASSUM ACCEPT_TAC;
           FIRST_ASSUM(fun th -> if is_forall (concl th) &&
               can (find_term ((=) `&457 / &500`)) (concl th)
             then MP_TAC (SPEC `4` th) THEN CONV_TAC C1089OD_EL_CONV THEN
                  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC
             else NO_TAC);
           MP_TAC (c1089se_cover C1089AC_SOUTHWEST_F_COVER) THEN CONV_TAC TAUT;
           MP_TAC (c1089se_cover C1089AC_SOUTHWEST_G_COVER) THEN CONV_TAC TAUT]));;

(* Lean: last_ne_pair *)
let C1089SE_LAST_NE_PAIR = prove
 (c1089wc_stmt []
    [c1089se_le (c1089wc_lcy 16384) `&2`; c1089se_le `&2` (c1089wc_lcx 32768)]
    (mk_conj(c1089se_own 1024 `&3` `&113 / &50`, c1089se_own 1024 `&3` `&12 / &5`)),
  c1089se_frame_tac [1024] THEN
  C1089WC_USE_TAC C1089SE_V C1089WC_SOUTHEAST_INWARD THEN
  C1089SE_AT_TAC C1089WC_TOP_HIGH `&113 / &50` THEN
  C1089SE_AT_TAC C1089WC_TOP_HIGH `&239 / &100` THEN
  C1089SE_HAVE_TAC (c1089se_own 1024 `&3` `&12 / &5`)
    (C1089SE_COVER_TAC C1089AC_NORTHEAST_G_COVER) THEN
  ASSUME_TAC (c1089se_cover C1089AC_NORTHEAST_F_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  C1089WC_APPLY_TAC (c1089wc_inst C1089SE_CLOCKWISE_PAIR (c1089wc_sw (c1089wc_tuple 1024))));;

(* Lean: last_left_pair *)
let C1089SE_LAST_LEFT_PAIR = prove
 (c1089wc_stmt [] [c1089se_le (c1089wc_lcy 16384) `&2`]
    (mk_conj(c1089se_own 4096 `&1` `&113 / &50`, c1089se_own 4096 `&1` `&12 / &5`)),
  c1089se_frame_tac [] THEN
  C1089WC_USE_TAC C1089SE_V C1089WC_SOUTHEAST_INWARD THEN
  C1089SE_AT_TAC C1089WC_SINGLETON_BAR `&8 / &5` THEN
  C1089SE_HAVE_TAC (c1089se_own 256 `&1` `&87 / &50`)
    (C1089SE_COVER_TAC C1089AC_SOUTHWEST_F_COVER) THEN
  C1089SE_HAVE_TAC (mk_neg (c1089se_own 4096 `&1` `&87 / &50`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089SE_V C1089DD_LEFT_PAIR THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: last_right_pair *)
let C1089SE_LAST_RIGHT_PAIR = prove
 (c1089wc_stmt []
    [c1089se_le (c1089wc_lcy 16384) `&2`; c1089se_le `&2` (c1089wc_lcx 32768)]
    (mk_conj(c1089se_own 16384 `&3` `&87 / &50`, c1089se_own 16384 `&3` `&8 / &5`)),
  c1089se_frame_tac [] THEN
  C1089WC_USE_TAC C1089SE_V C1089SE_LAST_NE_PAIR THEN
  C1089SE_HAVE_TAC (mk_neg (c1089se_own 16384 `&3` `&113 / &50`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089SE_V C1089DD_RIGHT_LOW_PAIR THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;
