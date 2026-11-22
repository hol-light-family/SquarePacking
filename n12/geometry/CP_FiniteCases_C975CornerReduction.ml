(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C975CornerReduction.lean           *)
(* (namespace N12Compact.FiniteCases.C975Selection).  Genuine singleton-     *)
(* corner reductions for C975 (no whole C975 exclusion).  owner p m is the   *)
(* 5-tuple (ooc .. m) .. l; statements are c975ic_stmt (hypotheses NPACK,    *)
(* IMAGE .. = c975d_family and the Lean premises, conjoined).                *)
(* C983.C974LocalData.Input = c983ld_input over (q).translated 1 1 /         *)
(* (pullSwap q).translated 1 1 (c983ld_tr / c983ld_sw), C974LocalEnding.     *)
(* impossible = C983LE_IMPOSSIBLE, SingletonMissing.zero/one_missing_points  *)
(* = CCSM_ZERO/ONE_MISSING_POINTS, WallProfile.boundary_origin =             *)
(* OCWPBO_BOUNDARY_ORIGIN; fixed / seed_point / aux_point = C975SS_* /       *)
(* c975ic_seed / c975ic_aux; bottom_origin, southeast_lower, left_reach =    *)
(* C975CP_*; southwest_south / west, bottom_reach = C975SS_*.  cap / markers *)
(* (private) are OO_SIDE_LE / OO_MARKERS.  Tag C975CR_.                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975CentralPoints.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;

let C975CR_NP = `NPACK c1 c2 a b l`;;
let C975CR_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c975d_family`;;
let c975cr_np = ASSUME C975CR_NP;;
let c975cr_hh = CONJ c975cr_np (ASSUME C975CR_IMG);;
(* |- !V5. NPACK /\ IMAGE [/\ h] ==> P  at the assumptions *)
let c975cr_inst th = MP (SPECL C975IC_V5 th) c975cr_hh;;
let c975cr_inst1 th h = MP (SPECL C975IC_V5 th) (CONJ c975cr_np (CONJ (ASSUME C975CR_IMG) h));;
let c975cr_apart m n = REWRITE_RULE[ldisj] (c975cr_inst (oo_apart C975D_F m n));;
(* ~ (owner m) x y from a point (x, y) of owner n *)
let c975cr_excl m n pt =
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] (c975cr_apart m n) in
  let qa = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH qa (MP (NOT_ELIM d2) (CONJ (ASSUME qa) pt)));;
let c975cr_unit m = MP (SPECL (C975IC_V5 @ [mk_small_numeral m]) OO_UNIT) c975cr_np;;
let c975cr_box m = MP (SPECL (C975IC_V5 @ [mk_small_numeral m]) OO_BOX) c975cr_np;;
let C975CR_SIDE = MP (SPECL C975IC_V5 OO_SIDE) c975cr_np;;

(* the SingletonMissing hypotheses for owner m in {1, 2} *)
let C975CR_SINGLETON_TAC m th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
  MP_TAC(SPECL C975IC_V5 OO_SIDE) THEN MP_TAC(SPECL C975IC_V5 OO_SIDE_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  MP_TAC(SPECL (C975IC_V5 @ [C975D_F; mk_small_numeral m]) OO_MARKERS) THEN
  ASM_REWRITE_TAC[in_fam m C975D_F] THEN
  REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM];;

(* Lean: missing_zero_seeds *)
let C975CR_MISSING_ZERO_SEEDS = prove
 (c975ic_stmt [mk_neg (c975ic_own 1 `&1` `&1`)]
    (mk_conj(c975ic_own 1 `&91 / &50` `&1`, c975ic_own 1 `&49 / &25` `&19 / &25`)),
  C975CR_SINGLETON_TAC 1 CCSM_ZERO_MISSING_POINTS);;

(* Lean: bottom_corner_input *)
let C975CR_BOTTOM_CORNER_INPUT =
  let missing = mk_neg (c975ic_own 1 `&1` `&1`) in
  let seeds = CONJUNCTS (c975cr_inst1 C975CR_MISSING_ZERO_SEEDS (ASSUME missing)) in
  let lower = c975cr_inst C975CP_SOUTHEAST_LOWER in
  let facts = [C975CR_SIDE; c975cr_inst (c975ic_seed 1 (`&1`, `&457 / &500`)); el 0 seeds; el 1 seeds;
               ASSUME missing; c975cr_inst C975CP_BOTTOM_ORIGIN;
               c975cr_inst C975SS_BOTTOM_MARKER;
               CONJUNCT1 (c975cr_inst C975SS_BOTTOM_REACH);
               c975cr_excl 8192 512 (c975cr_inst C975SS_SE_MARKER);
               c975cr_excl 8192 256 (c975cr_inst C975SS_SOUTHWEST_SOUTH);
               c975cr_excl 8192 512 lower;
               c975cr_inst C975SS_SE_CORNER; c975cr_excl 12 512 lower;
               c975cr_apart 1 8192; c975cr_apart 1 12; c975cr_apart 8192 12] in
  prove
   (c975ic_stmt [missing]
      (c983ld_concl (c983ld_tr (c975ic_owner 1)) (c983ld_tr (c975ic_owner 8192))
                    (c983ld_tr (c975ic_owner 12))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (c975cr_box 1); REWRITE_RULE[lcont] (c975cr_box 12)]);;

(* C983LE_IMPOSSIBLE at three owner tuples, from the Input theorem *)
let c975cr_close tK tW tC ms inth =
  let units = map c975cr_unit ms in
  let pos = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) C975CR_SIDE in
  let th = SPECL (tK @ tW @ tC) C983LE_IMPOSSIBLE in
  MP th (TAC_PROOF(([], lhand (concl th)),
    REPEAT CONJ_TAC THEN
    FIRST [ACCEPT_TAC pos; ACCEPT_TAC inth; MAP_EVERY MP_TAC units THEN REAL_ARITH_TAC]));;

(* Lean: singleton_zero_corner *)
let C975CR_SINGLETON_ZERO_CORNER =
  let missing = mk_neg (c975ic_own 1 `&1` `&1`) in
  let inth = c975cr_inst1 C975CR_BOTTOM_CORNER_INPUT (ASSUME missing) in
  let th = c975cr_close (c983ld_tr (c975ic_owner 1)) (c983ld_tr (c975ic_owner 8192))
             (c983ld_tr (c975ic_owner 12)) [1; 8192; 12] inth in
  prove
   (c975ic_stmt [] (c975ic_own 1 `&1` `&1`),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REFUTE_THEN (fun h -> ACCEPT_TAC (PROVE_HYP h th)));;

(* Lean: singleton_one_missing_corner *)
let C975CR_SINGLETON_ONE_MISSING_CORNER =
  let th = c975cr_excl 2 1 (c975cr_inst C975CR_SINGLETON_ZERO_CORNER) in
  prove(c975ic_stmt [] (concl th), REPEAT GEN_TAC THEN STRIP_TAC THEN ACCEPT_TAC th);;

(* Lean: singleton_one_strong *)
let C975CR_SINGLETON_ONE_STRONG =
  let one = prove
   (c975ic_stmt [mk_neg (c975ic_own 2 `&1` `&1`)]
      (mk_conj(c975ic_own 2 `&1` `&91 / &50`, c975ic_own 2 `&19 / &25` `&49 / &25`)),
    C975CR_SINGLETON_TAC 2 CCSM_ONE_MISSING_POINTS) in
  let th = c975cr_inst1 one (c975cr_inst C975CR_SINGLETON_ONE_MISSING_CORNER) in
  prove(c975ic_stmt [] (concl th), REPEAT GEN_TAC THEN STRIP_TAC THEN ACCEPT_TAC th);;

(* Lean: left_origin_of_top_halfpoint *)
let C975CR_LEFT_ORIGIN_OF_TOP_HALFPOINT = prove
 (c975ic_stmt [c975ic_own 34816 `&3 / &2` `&3`] (c975ic_own 4096 `&1` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC OCWPBO_BOUNDARY_ORIGIN
    (c975ss_pullsw (c975ss_pully (c975ic_owner 4096)) @
     c975ss_pullsw (c975ss_pully (c975ic_owner 192)) @ [`&457 / &500`; `&8 / &5`])
   [C975IP_L_MARKER; C975IP_L_HIGH; c975ic_seed 192 (`&457 / &500`, `&3`);
    c975ic_seed 192 (`&1`, `&3`)]
   [34816, TRUTH]
   [C975CP_WALL_TAC 4096; C975CP_WALL_TAC 192;
    REWRITE_TAC[ldisj; LINSIDE_PULLSW; LINSIDE_PULLY] THEN
    MP_TAC (SPEC_ALL (oo_apart C975D_F 192 4096)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: left_corner_input *)
let C975CR_LEFT_CORNER_INPUT =
  let top = c975ic_own 34816 `&3 / &2` `&3` in
  let topth = ASSUME top in
  let seeds = CONJUNCTS (c975cr_inst C975CR_SINGLETON_ONE_STRONG) in
  let facts = [C975CR_SIDE; c975cr_inst (c975ic_seed 2 (`&457 / &500`, `&1`)); el 0 seeds; el 1 seeds;
               c975cr_inst C975CR_SINGLETON_ONE_MISSING_CORNER;
               c975cr_inst1 C975CR_LEFT_ORIGIN_OF_TOP_HALFPOINT topth;
               c975cr_inst C975IP_L_MARKER; c975cr_inst C975CP_LEFT_REACH;
               c975cr_excl 4096 34816 (c975cr_inst C975SS_NW_MARKER);
               c975cr_excl 4096 256 (c975cr_inst C975SS_SOUTHWEST_WEST);
               c975cr_excl 4096 34816 topth;
               c975cr_inst (c975ic_seed 192 (`&1`, `&3`)); c975cr_excl 192 34816 topth;
               c975cr_apart 2 4096; c975cr_apart 2 192; c975cr_apart 4096 192] in
  let tr t = c983ld_tr (c983ld_sw t) in
  prove
   (c975ic_stmt [top]
      (c983ld_concl (tr (c975ic_owner 2)) (tr (c975ic_owner 4096)) (tr (c975ic_owner 192))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (c975cr_box 2); REWRITE_RULE[lcont] (c975cr_box 192)]);;

(* Lean: top_halfpoint_excluded *)
let C975CR_TOP_HALFPOINT_EXCLUDED =
  let top = c975ic_own 34816 `&3 / &2` `&3` in
  let tr t = c983ld_tr (c983ld_sw t) in
  let inth = c975cr_inst1 C975CR_LEFT_CORNER_INPUT (ASSUME top) in
  let th = c975cr_close (tr (c975ic_owner 2)) (tr (c975ic_owner 4096)) (tr (c975ic_owner 192))
             [2; 4096; 192] inth in
  prove
   (c975ic_stmt [] (mk_neg top),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun h -> ACCEPT_TAC (PROVE_HYP h th)));;
