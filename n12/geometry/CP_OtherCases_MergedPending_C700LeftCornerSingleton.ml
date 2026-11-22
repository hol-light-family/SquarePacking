(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/C700LeftCornerSingleton*)
(* .lean (namespace N12Compact.MergedPending).  The actual left singleton    *)
(* must own the southwest corner in C700.  family .c700 is mpf_family_c700;  *)
(* owner p m is mpwr_tuple m (WallReach.ml mpwr_ helpers); C974LocalData.    *)
(* Input is c983ld_input over (pullSwap q).translated 1 1 =                  *)
(* c983ld_tr (c983ld_sw q) (closed with C983LD_CLOSE_TAC);                   *)
(* C974LocalEnding.impossible C983LE_IMPOSSIBLE; SingletonMissing.           *)
(* one_missing_points CCSM_ONE_MISSING_POINTS (exact markers from            *)
(* OO_MARKERS); left_reach / top_reach MPWR_LEFT_REACH / MPWR_TOP_REACH;     *)
(* southwest_crosspoints MPCP_SOUTHWEST_CROSSPOINTS; c700_left_origin        *)
(* MPCOO_C700_LEFT_ORIGIN.  Tag MPLCS_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_C700OppositeOrigins.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_CentralPoints.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;

let MPLCS_FAM = `mpf_family_c700`;;
let mplcs_unit_of uth t =
  let c = el 0 t and s = el 1 t in
  let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                   (mk_binop `( * ):real->real->real` s s), `&1`) in
  MP (prove(mk_imp(concl uth, tm), CONV_TAC REAL_RING)) uth;;
let mplcs_t m = c983ld_tr (c983ld_sw (mpwr_tuple m));;
let MPLCS_HYPS = list_mk_conj [mk_neg (mpwr_inside 2 `&1` `&1`); mpwr_inside 2 `&1` `&91 / &50`;
                               mpwr_inside 2 `&19 / &25` `&49 / &25`];;

(* Lean: c700_left_missing_input *)
let MPLCS_C700_LEFT_MISSING_INPUT = prove
 (mpwr_stmt MPLCS_FAM (mk_imp(MPLCS_HYPS,
    list_mk_comb(`c983ld_input`, mplcs_t 2 @ mplcs_t 4096 @ mplcs_t 192))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  let fam = MPLCS_FAM in
  let np = mpwr_np fam in
  let box m = REWRITE_RULE[lcont] (MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_BOX) np) in
  let side = MP (SPECL MPWR_VARS OO_SIDE) np in
  let apart m n = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam m n)) in
  let far = mpwr_bar (CONJUNCT2 (mpwr_inst fam (el 1 MPWR_LEFT_REACH))) `&14 / &5` in
  let middle = CONJUNCT2 (mpwr_inst fam (el 1 MPCP_SOUTHWEST_CROSSPOINTS)) in
  let outer = mpwr_bar (CONJUNCT2 (mpwr_inst fam (el 1 MPWR_TOP_REACH))) `&3 / &2` in
  let hs = CONJUNCTS (ASSUME MPLCS_HYPS) in
  let facts = hs @
    [side; mpwr_seed fam 2 (`&457 / &500`, `&1`); mpwr_seed fam 4096 (`&457 / &500`, `&2`);
     mpwr_seed fam 192 (`&1`, `&3`); mpwr_missing fam 4096 11;
     mpwr_inst fam MPCOO_C700_LEFT_ORIGIN; far;
     mpwr_excl fam 4096 256 middle; mpwr_excl fam 4096 32768 outer;
     mpwr_excl fam 192 32768 outer;
     apart 2 4096; apart 2 192; apart 4096 192] in
  C983LD_CLOSE_TAC facts [box 2; box 4096; box 192]);;

(* Lean: c700_left_singleton_corner *)
let MPLCS_C700_LEFT_SINGLETON_CORNER = prove
 (mpwr_stmt MPLCS_FAM (mpwr_inside 2 `&1` `&1`),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let fam = MPLCS_FAM in
  let np = mpwr_np fam in
  let unit m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let side = MP (SPECL MPWR_VARS OO_SIDE) np in
  let missing = ASSUME (mk_neg (mpwr_inside 2 `&1` `&1`)) in
  SUBGOAL_THEN (mk_conj(mpwr_inside 2 `&1` `&91 / &50`, mpwr_inside 2 `&19 / &25` `&49 / &25`))
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CCSM_ONE_MISSING_POINTS THEN ASM_SIMP_TAC[OO_UNIT; OO_BOX; missing] THEN
    MP_TAC(SPECL MPWR_VARS OO_SIDE) THEN MP_TAC(SPECL MPWR_VARS OO_SIDE_LE) THEN
    REWRITE_TAC[np] THEN REPEAT DISCH_TAC THEN REWRITE_TAC[MP (SPECL (MPWR_VARS @ [`2`]) OO_BOX) np] THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    MP_TAC(SPECL (MPWR_VARS @ [fam; `2`]) OO_MARKERS) THEN
    REWRITE_TAC[np; CONJUNCT2 (ASSUME (mpwr_hyp fam)); in_fam 2 fam] THEN
    REWRITE_TAC[bitset_bits 2; IN_SET_OF_LIST; MEM];
    ALL_TAC] THEN
  let tK = mplcs_t 2 and tW = mplcs_t 4096 and tC = mplcs_t 192 in
  let pu m t = mplcs_unit_of (unit m) t in
  MP_TAC(SPECL (tK @ tW @ tC) C983LE_IMPOSSIBLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ACCEPT_TAC (pu 2 tK); MP_TAC side THEN REAL_ARITH_TAC;
      ACCEPT_TAC (pu 4096 tW); MP_TAC side THEN REAL_ARITH_TAC;
      ACCEPT_TAC (pu 192 tC); MP_TAC side THEN REAL_ARITH_TAC;
      MP_TAC(SPECL MPWR_VARS MPLCS_C700_LEFT_MISSING_INPUT) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;
