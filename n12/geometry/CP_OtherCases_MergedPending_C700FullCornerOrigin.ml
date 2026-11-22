(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/C700FullCornerOrigin *)
(* .lean (namespace N12Compact.MergedPending).  C700's actual paired         *)
(* southeast corner forces the right-wall origin (and, by the perpendicular  *)
(* transfer, the bottom-wall origin).  family .c700 is mpf_family_c700;      *)
(* owner p m is the OriginalOwners tuple (mpwr_tuple m); seed / apart /      *)
(* box / side: oo_seed / oo_apart / OO_BOX / OO_SIDE (through the mpwr_*     *)
(* helpers of WallReach.ml); bottom_reach / c700_right_reach: MPWR_BOTTOM_   *)
(* REACH (c700 entry) / MPWR_C700_RIGHT_REACH; WallProfile.boundary_origin:  *)
(* OCWPBO_BOUNDARY_ORIGIN.  The pulled squares pullSwap (pullX q) and        *)
(* pullX q are the explicit 5-tuples of p2_base (LINSIDE_PULLX/SW).          *)
(* Tag MPFCO_.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_WallReach.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

(* pullX and pullSwap on a 5-tuple of terms *)
let mpfco_pullx [c; s; u; v; a] =
  [mk_comb(`(--):real->real`, c); s; mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` c);
   mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a)
     (mk_binop `( * ):real->real->real` `&4` s); a];;
let mpfco_pullsw [c; s; u; v; a] =
  [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a];;

(* apply boundary_origin to the pulled owners  pull(owner mq), pull(owner mk) *)
let mpfco_origin fam pull mq mk facts concl =
  let np = mpwr_np fam in
  let unit m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let box m = REWRITE_RULE[lcont] (MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_BOX) np) in
  let side = MP (SPECL MPWR_VARS OO_SIDE) np in
  let apart = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam mk mq)) in
  let gth = SPECL (pull (mpwr_tuple mq) @ pull (mpwr_tuple mk) @ [`&457 / &500`; `&8 / &5`])
                  OCWPBO_BOUNDARY_ORIGIN in
  let gth1 = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLSW; ldisj] THENC
                        REAL_RAT_REDUCE_CONV) gth in
  let solve =
    FIRST (map (fun t -> t THEN NO_TAC)
          [FIRST (map ACCEPT_TAC (side :: facts));
           REAL_ARITH_TAC;
           MP_TAC side THEN REAL_ARITH_TAC;
           MP_TAC (unit mq) THEN REAL_ARITH_TAC;
           MP_TAC (unit mk) THEN REAL_ARITH_TAC;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (box mq)) THEN REAL_ARITH_TAC;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (box mk)) THEN REAL_ARITH_TAC;
           REWRITE_TAC[apart]]) in
  let th = TAC_PROOF(([], mk_imp(mpwr_hyp fam, concl)),
    DISCH_TAC THEN MP_TAC gth1 THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN solve; ALL_TAC] THEN
    CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]) in
  GENL MPWR_VARS th;;

let MPFCO_FAM = `mpf_family_c700`;;
let MPFCO_BOTTOM = mpwr_inst MPFCO_FAM (el 1 MPWR_BOTTOM_REACH);;
let MPFCO_RIGHT = mpwr_inst MPFCO_FAM MPWR_C700_RIGHT_REACH;;
let mpfco_reach th t = mpwr_bar (CONJUNCT2 th) t;;

(* Lean: c700_right_origin *)
let MPFCO_C700_RIGHT_ORIGIN =
  let fam = MPFCO_FAM in
  let marker = mpwr_seed fam 16384 (`&1543 / &500`, `&2`) in
  let corner_marker = mpwr_seed fam 12 (`&1543 / &500`, `&1`) in
  let corner = mpwr_seed fam 12 (`&3`, `&1`) in
  let reach = mpfco_reach MPFCO_RIGHT `&8 / &5` in
  let omitted = mpwr_excl fam 12 8192 (mpfco_reach MPFCO_BOTTOM `&5 / &2`) in
  mpfco_origin fam (fun q -> mpfco_pullsw (mpfco_pullx q)) 16384 12
    [marker; corner_marker; corner; reach; omitted] (mpwr_inside 16384 `&3` `&2`);;

(* Lean: c700_bottom_origin *)
let MPFCO_C700_BOTTOM_ORIGIN =
  let fam = MPFCO_FAM in
  let marker = mpwr_seed fam 8192 (`&2`, `&457 / &500`) in
  let corner_marker = mpwr_seed fam 12 (`&3`, `&457 / &500`) in
  let corner = mpwr_seed fam 12 (`&3`, `&1`) in
  let reach = mpfco_reach MPFCO_BOTTOM `&12 / &5` in
  let omitted = mpwr_excl fam 12 16384 (mpfco_reach MPFCO_RIGHT `&3 / &2`) in
  mpfco_origin fam mpfco_pullx 8192 12
    [marker; corner_marker; corner; reach; omitted] (mpwr_inside 8192 `&2` `&1`);;
