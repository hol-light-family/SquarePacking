(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/MergedTopExclusion.lean.      *)
(* The actual merged western owner (owners p 7 = owner 2304) cannot reach   *)
(* F3.  actual p i = c983e_actual c1 c2 a b l i (Entrance); owners p 6 =    *)
(* owner 1024, owners p 8 = owner 4096.  MergedTopExclusion.impossible =    *)
(* OCMTE_IMPOSSIBLE; left_bar = C983AB_LEFT_BAR.  Tag C983MTE_.              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_ActualBars.ml";;
needs "n12/geometry/CP_OtherCases_MergedTopExclusion.ml";;

(* Lean: merged_no_f3 *)
let C983MTE_MERGED_NO_F3 =
  let f3tm = `3 IN c983e_actual c1 c2 a b l 7` in
  let f3 = CONV_RULE (REWRITE_CONV[c983e_actual; c983ri_owner_code] THENC ONCE_DEPTH_CONV EL_CONV)
             (ASSUME f3tm) in
  let top = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (c983ab_point 3 f3) in
  let unit, pos, side, _ = c983ab_basics 2304 in
  let cap = MP (SPECL C983E_VARS OO_SIDE_LE) (CONJUNCT1 (ASSUME C983AB_H)) in
  let marker = c983ab_seed 7 `&33 / &20` `&33 / &20` in
  let ne = c983ab_excl 2304 1024 6 `&47 / &20` `&47 / &20` in
  let bar =
    let apart = REWRITE_RULE[ldisj] (c983ab_mp (oo_apart C983E_F 2304 4096)) in
    let lb = c983ab_mp C983AB_LEFT_BAR in
    UNDISCH (prove(mk_imp(C983AB_H, mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &12 / &5`,
            mk_neg(c983ab_in 2304 `&1` `y:real`))))),
          DISCH_TAC THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
          MP_TAC(SPECL [`&1`; `y:real`] apart) THEN MP_TAC(SPEC `y:real` lb) THEN
          ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
           [UNDISCH_TAC `y <= &12 / &5` THEN REAL_ARITH_TAC; SIMP_TAC[]])) in
  let fth = MP (SPECL (c983ab_own 2304) OCMTE_IMPOSSIBLE)
               (end_itlist CONJ [unit; pos; side; cap; marker; top; ne; bar]) in
  c983ab_gen (NOT_INTRO (DISCH f3tm fth));;
