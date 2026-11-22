(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardNeighbors.lean                 *)
(* (N12Compact.C1092MPPMInwardNeighbors).  An actual inward southwest owner  *)
(* in the zero-omission entrance has two actual ordinary neighbors.          *)
(* Conventions of CP_C1092_MPPMCentralCover.ml (Inward is c1092mcc_inward;   *)
(* owners p i at mask EL i c1092wc_code, side l; Missing is c1092mom_missing;*)
(* the c1092mo_ layer toolkit of CP_C1092_MMMP_Origins.ml builds the pulled  *)
(* owners: Transform.pull (T,T,T) q = pullSwap (pullY (pullX q)), with       *)
(* inside (4 - y) (4 - x)).  Covers: C1092MMEN_SOUTHEAST_F_COVER,            *)
(* C1092AC_SOUTHEAST_G_COVER, C1092AC_NORTHWEST_F_COVER / _G_COVER;          *)
(* MixedSpan.impossible C1092MS_IMPOSSIBLE; WallLowerReach.point WLR_POINT;  *)
(* C981CompletionCrosspoint.point C981CP_POINT; ElbowPoint.points_original   *)
(* OCEP_POINTS_ORIGINAL; inside_segment C1092WC_INSIDE_SEGMENT.              *)
(* Tag C1092MIN_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMCentralCover.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/CP_C1092_MMMMEntrance.ml";;

(* Lean: side_gt (private) *)
let C1092MIN_SIDE_GT = C1092MPPE_SIDE_GT;;
(* Lean: marker_point (private): markers are oo_seed points (c1092mo_seed) *)

let C1092MIN_HYPS = Printf.sprintf "%s /\\ %s /\\ (!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k) /\\ c1092mcc_inward %s"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4;;
let c1092min_stmt concl = parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MIN_HYPS concl);;

(* walls, the inward points and the earlier results ths in the assumptions, literal masks *)
let C1092MIN_START_TAC ths =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MOM_ORDINARY_WALLS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) ths THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcc_inward] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mcc_inward`)) THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV);;

let c1092min_a i x y = ASSUME (c1092mo_in i x y);;
let c1092min_useh th = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th) (c1092mo_hh ()));;
let C1092MIN_G = [C1092MO_X; C1092MO_Y; C1092MO_SW];;

(* Lean: southeast_pair *)
let C1092MIN_SOUTHEAST_PAIR = prove
 (c1092min_stmt (c1092mppe_in 5 "&12 / &5" "&1" ^ " /\\ " ^ c1092mppe_in 5 "&113 / &50" "&1"),
  C1092MIN_START_TAC [] THEN
  let inw1 = c1092min_a 4 `&2` `&87 / &50` in
  let rightF = c1092min_a 10 `&3` `&87 / &50` and rightG = c1092min_a 10 `&3` `&8 / &5` in
  let fcov = c1092min_useh C1092MMEN_SOUTHEAST_F_COVER and gcov = c1092min_useh C1092AC_SOUTHEAST_G_COVER in
  let e4 = c1092mo_excl 5 4 inw1 and eF = c1092mo_excl 5 10 rightF and eG = c1092mo_excl 5 10 rightG in
  let t, eqs = c1092mo_layers 5 C1092MIN_G in
  let hc = c1092mo_in 5 `&113 / &50` `&2` and hf = c1092mo_in 5 `&12 / &5` `&1`
  and ha = mk_neg (c1092mo_in 5 `&113 / &50` `&1`) in
  let ms = itlist DISCH [hc; hf; ha]
    (c1092mo_apply (c1092mo_conv eqs) (SPECL t C1092MS_IMPOSSIBLE)
      [c1092mo_punit 5 t; c1092mo_pos (); c1092mo_side (); ASSUME hc; ASSUME hf; ASSUME ha; e4; eF; eG]) in
  MP_TAC (end_itlist CONJ [fcov; gcov; e4; eF; eG; ms]) THEN CONV_TAC TAUT);;

(* Lean: bottom_far *)
let C1092MIN_BOTTOM_FAR = prove
 (c1092min_stmt (c1092mppe_in 9 "&36 / &25" "&1"),
  C1092MIN_START_TAC [C1092MIN_SOUTHEAST_PAIR] THEN
  let layers = [C1092MO_X; C1092MO_SW] in
  let t, eqs = c1092mo_layers 9 layers in
  ACCEPT_TAC (c1092mo_apply (c1092mo_conv eqs) (SPECL t WLR_POINT)
    [c1092mo_punit 9 t; c1092mo_side (); c1092mo_plcont 9 layers;
     c1092mo_seed 9 (`&2`, `&457 / &500`); c1092min_a 9 `&8 / &5` `&1`;
     c1092mo_excl 9 5 (c1092min_a 5 `&113 / &50` `&1`);
     c1092mo_excl 9 4 (c1092min_a 4 `&2` `&87 / &50`)]));;

(* Lean: bottom_halfpoint *)
let C1092MIN_BOTTOM_HALFPOINT = prove
 (c1092min_stmt (c1092mppe_in 9 "&3 / &2" "&1"),
  C1092MIN_START_TAC [C1092MIN_BOTTOM_FAR] THEN
  ACCEPT_TAC (CONV_RULE REAL_RAT_REDUCE_CONV (MATCH_MP C1092WC_INSIDE_SEGMENT
    (end_itlist CONJ [c1092min_a 9 `&36 / &25` `&1`; c1092min_a 9 `&8 / &5` `&1`;
      REAL_ARITH `&0 <= &3 / &8`; REAL_ARITH `&3 / &8 <= &1`]))));;

(* Lean: southwest_crosspoint *)
let C1092MIN_SOUTHWEST_CROSSPOINT = prove
 (c1092min_stmt (c1092mppe_in 4 "&3 / &2" "&2"),
  C1092MIN_START_TAC [C1092MIN_BOTTOM_HALFPOINT] THEN
  let t, eqs = c1092mo_layers 4 C1092MIN_G in
  ACCEPT_TAC (c1092mo_apply (c1092mo_conv eqs) (SPECL t C981CP_POINT)
    [c1092mo_punit 4 t; c1092mo_pos (); c1092mo_side ();
     c1092min_a 4 `&87 / &50` `&2`; c1092min_a 4 `&2` `&87 / &50`;
     c1092mo_seed 4 (`&33 / &20`, `&33 / &20`);
     c1092mo_excl 4 5 (c1092mo_seed 5 (`&47 / &20`, `&33 / &20`));
     c1092mo_excl 4 7 (c1092mo_seed 7 (`&33 / &20`, `&47 / &20`));
     c1092mo_excl 4 9 (c1092min_a 9 `&8 / &5` `&1`);
     c1092mo_excl 4 9 (c1092min_a 9 `&3 / &2` `&1`)]));;

(* Lean: northwest_pair *)
let C1092MIN_NORTHWEST_PAIR = prove
 (c1092min_stmt (c1092mppe_in 7 "&8 / &5" "&3" ^ " /\\ " ^ c1092mppe_in 7 "&87 / &50" "&3"),
  C1092MIN_START_TAC [C1092MIN_SOUTHWEST_CROSSPOINT] THEN
  let fcov = c1092min_useh C1092AC_NORTHWEST_F_COVER and gcov = c1092min_useh C1092AC_NORTHWEST_G_COVER in
  let ew1 = c1092mo_excl 7 8 (c1092min_a 8 `&1` `&113 / &50`)
  and ew2 = c1092mo_excl 7 8 (c1092min_a 8 `&1` `&12 / &5`)
  and e4 = c1092mo_excl 7 4 (c1092min_a 4 `&87 / &50` `&2`) in
  let t, eqs = c1092mo_layers 7 [C1092MO_SW] in
  let he = c1092mo_in 7 `&2` `&113 / &50` and hg = c1092mo_in 7 `&87 / &50` `&3`
  and ha = mk_neg (c1092mo_in 7 `&8 / &5` `&3`) in
  let pts = c1092mo_apply (c1092mo_conv eqs) (SPECL t OCEP_POINTS_ORIGINAL)
    [c1092mo_punit 7 t; c1092mo_side (); c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
     ASSUME he; ASSUME hg; ASSUME ha;
     c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
     c1092mo_excl 7 11 (c1092mo_seed 11 (`&2`, `&1543 / &500`))] in
  let contra = itlist DISCH [he; hg; ha]
    (MP (NOT_ELIM (c1092mo_excl 7 4 (c1092min_a 4 `&3 / &2` `&2`))) (CONJUNCT1 pts)) in
  MP_TAC (end_itlist CONJ [fcov; gcov; ew1; ew2; e4; contra]) THEN CONV_TAC TAUT);;
