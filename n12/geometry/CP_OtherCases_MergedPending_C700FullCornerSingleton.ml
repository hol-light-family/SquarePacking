(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/C700FullCornerSingleton*)
(* .lean (namespace N12Compact.MergedPending).  C700's actual bottom         *)
(* singleton owns the southwest corner.  family .c700 is mpf_family_c700;    *)
(* owner p m is mpwr_tuple m (WallReach.ml mpwr_ helpers); C974LocalData.   *)
(* Input is c983ld_input over the translated tuples c983ld_tr (closed with   *)
(* C983LD_CLOSE_TAC); C974LocalEnding.impossible C983LE_IMPOSSIBLE;          *)
(* SingletonMissing.zero_missing_points CCSM_ZERO_MISSING_POINTS (exact      *)
(* markers from OO_MARKERS); southwest_crosspoints MPCP_SOUTHWEST_CROSSPOINTS;*)
(* c700_right_reach MPWR_C700_RIGHT_REACH; bottom_reach MPWR_BOTTOM_REACH;   *)
(* c700_bottom_origin MPFCO_C700_BOTTOM_ORIGIN.  Tag MPFCS_.                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_CentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_C700FullCornerOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;

let MPFCS_FAM = `mpf_family_c700`;;

(* c * c + s * s = &1 for a tuple t from the owner's unit normal *)
let mpfcs_unit_of uth t =
  let c = el 0 t and s = el 1 t in
  let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                   (mk_binop `( * ):real->real->real` s s), `&1`) in
  MP (prove(mk_imp(concl uth, tm), CONV_TAC REAL_RING)) uth;;

(* the SingletonMissing seeds of the singleton owner m (statement under mpwr_hyp) *)
let mpfcs_seeds fam m lemma concl =
  prove(mpwr_stmt fam (mk_imp(mk_neg (mpwr_inside m `&1` `&1`), concl)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN
    ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
    MP_TAC(SPECL MPWR_VARS OO_SIDE) THEN MP_TAC(SPECL MPWR_VARS OO_SIDE_LE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    MP_TAC(SPECL (MPWR_VARS @ [fam; mk_small_numeral m]) OO_MARKERS) THEN
    ASM_REWRITE_TAC[in_fam m fam] THEN
    REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM]);;

let MPFCS_SEEDS = mpfcs_seeds MPFCS_FAM 1 CCSM_ZERO_MISSING_POINTS
  (mk_conj(mpwr_inside 1 `&91 / &50` `&1`, mpwr_inside 1 `&49 / &25` `&19 / &25`));;

(* Lean: c700_bottom_singleton_corner *)
let MPFCS_C700_BOTTOM_SINGLETON_CORNER = prove
 (mpwr_stmt MPFCS_FAM (mpwr_inside 1 `&1` `&1`),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let fam = MPFCS_FAM in
  let np = mpwr_np fam in
  let box m = REWRITE_RULE[lcont] (MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_BOX) np) in
  let unit m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let side = MP (SPECL MPWR_VARS OO_SIDE) np in
  let apart m n = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam m n)) in
  let missing = ASSUME (mk_neg (mpwr_inside 1 `&1` `&1`)) in
  let strong = MP (mpwr_inst fam MPFCS_SEEDS) missing in
  let middle = CONJUNCT1 (mpwr_inst fam (el 1 MPCP_SOUTHWEST_CROSSPOINTS)) in
  let right = mpwr_bar (CONJUNCT2 (mpwr_inst fam MPWR_C700_RIGHT_REACH)) `&3 / &2` in
  let far = mpwr_bar (CONJUNCT2 (mpwr_inst fam (el 1 MPWR_BOTTOM_REACH))) `&14 / &5` in
  let facts =
    [side; missing; CONJUNCT1 strong; CONJUNCT2 strong;
     mpwr_seed fam 1 (`&1`, `&457 / &500`); mpwr_seed fam 8192 (`&2`, `&457 / &500`);
     mpwr_seed fam 12 (`&3`, `&1`); mpwr_missing fam 8192 9;
     mpwr_inst fam MPFCO_C700_BOTTOM_ORIGIN; far;
     mpwr_excl fam 8192 256 middle; mpwr_excl fam 8192 16384 right;
     mpwr_excl fam 12 16384 right;
     apart 1 8192; apart 1 12; apart 8192 12] in
  let tK = c983ld_tr (mpwr_tuple 1) and tW = c983ld_tr (mpwr_tuple 8192)
  and tC = c983ld_tr (mpwr_tuple 12) in
  let pu m t = mpfcs_unit_of (unit m) t in
  MP_TAC(SPECL (tK @ tW @ tC) C983LE_IMPOSSIBLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ACCEPT_TAC (pu 1 tK); MP_TAC side THEN REAL_ARITH_TAC;
      ACCEPT_TAC (pu 8192 tW); MP_TAC side THEN REAL_ARITH_TAC;
      ACCEPT_TAC (pu 12 tC); MP_TAC side THEN REAL_ARITH_TAC;
      C983LD_CLOSE_TAC facts [box 1; box 8192; box 12]];
    REWRITE_TAC[]]);;
