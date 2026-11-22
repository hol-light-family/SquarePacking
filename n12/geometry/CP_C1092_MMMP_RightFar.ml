(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/RightFar.lean                       *)
(* (N12Compact.C1092MMMPRightFar).  Actual MMMP right G8 forces G9.          *)
(* Conventions of CP_C1092_MMMP_SoutheastSign.ml (PositiveActual E is        *)
(* c1092mss_positiveActual; forward toolkit c1092mo_ functions).  The squares of the  *)
(* Lean proof are explicit tuples: for E = (cE, sE, uE, vE, aE),             *)
(*   C = swap E = (cE, --sE, vE, uE, aE)                 (C1092MRF_INSIDE_C), *)
(*   A = translate (swap C) (-2) (-2) = translate E (-2) (-2)                *)
(*     = (cE, sE, uE + 2cE + 2sE, vE + 2cE - 2sE, aE)    (C1092MRF_INSIDE_A), *)
(*   W = (pullY (owners p 10)).translated 2 2 = (c, --s, u - 2c - 2s,        *)
(*       2c - 2s - v - a, a) for owners p 10 = (c, s, u, v, a)               *)
(*                                     (C1092MRF_INSIDE_W, C1092MRF_CENTER_W),*)
(*   R = pullSwap (pullY (owners p 9)) via the c1092mo_ layers.              *)
(* InwardMissingProfile.Profile / profile: C1092IMP_profile / C1092IMP_PROFILE*)
(* MixedWideCrossing.point C1092MWC_POINT; InwardCrossingConflict.impossible *)
(* C1092ICC_IMPOSSIBLE; RightInnerActual.right_missing_inner                  *)
(* C1092MRIA_RIGHT_MISSING_INNER; right_g_cover C1092AC_RIGHT_G_COVER;        *)
(* p.side_le is OO_SIDE_LE.  Tag C1092MRF_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_SoutheastSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightInnerActual.ml";;
needs "n12/geometry/CP_C1092_MixedWideCrossing.ml";;
needs "n12/geometry/CP_C1092_InwardMissingProfile.ml";;
needs "n12/geometry/CP_C1092_InwardCrossingConflict.ml";;

let C1092MRF_INSIDE_C = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1092MRF_INSIDE_A = prove
 (`forall c s u v a x y. linside c s (u + &2 * c + &2 * s) (v + &2 * c - &2 * s) a x y <=>
                   linside c s u v a (x - &2) (y - &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1092MRF_INSIDE_W = prove
 (`forall c s u v a x y. linside c (--s) (u - &2 * c - &2 * s) (&2 * c - &2 * s - v - a) a x y <=>
                   linside c s u v a (&2 + x) (&2 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1092MRF_CENTER_W = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy c (--s) (u - &2 * c - &2 * s) (&2 * c - &2 * s - v - a) a = &2 - lcy c s u v a`,
  REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING);;
let C1092MRF_ANGLE = prove
 (`forall c s. &0 < c /\ c * c + s * s = &1
     ==> C1092WPS_half c s * (&1 + c) = s /\ s * C1092WPS_half c s = &1 - c /\
         (&1 + c) * C1092WPS_half c s = s`,
  REWRITE_TAC[C1092WPS_half] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_FIELD);;

(* the EL-form owner tuple of slot i *)
let c1092mrf_el i = fst (chop_list 5 (snd (strip_comb (parse_term (c1092mmpe_in i "x" "y")))));;

(* Lean: near_of_lower *)
let C1092MRF_NEAR_OF_LOWER = prove
 (parse_term (Printf.sprintf "!%s. NPACK %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_P C1092MMPE_CTX
    (c1092mmpe_in 10 "&3" "&8 / &5") C1092MSS_NEAR),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MMPE_WALL_AUXILIARIES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (c1092mrf_el 10 @ [`&3`; `&8 / &5`; `&3`; `&113 / &50`; `&7 / &33`]) C1092WC_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let C1092MRF_LOWER = c1092mmpe_in 10 "&3" "&8 / &5";;

(* Lean: upper_of_lower *)
let C1092MRF_UPPER_OF_LOWER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MRF_LOWER (c1092mmpe_in 10 "&3" "&12 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MRF_NEAR_OF_LOWER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_INWARD_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[c1092mss_positiveActual] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let lit s = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term s)) in
  let lower = lit C1092MRF_LOWER and near = lit C1092MSS_NEAR in
  let bottom = c1092mo_use C1092MBP_PAIR in
  let nwc = c1092mo_use C1092MPC_NORTHWEST_CENTER in
  let tip10 = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MBP_RIGHT_TIP)) in
  let o10 = c1092mo_own 10 in
  let [c10; s10; u10; v10; a10] = o10 in
  let tW = [c10; mk_comb(`(--):real->real`, s10);
            mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` u10 (mk_binop `( * ):real->real->real` `&2` c10)) (mk_binop `( * ):real->real->real` `&2` s10);
            mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_binop `( * ):real->real->real` `&2` c10) (mk_binop `( * ):real->real->real` `&2` s10)) v10) a10; a10] in
  let insW = SPECL o10 C1092MRF_INSIDE_W in
  let centerW = MATCH_MP (SPECL o10 C1092MRF_CENTER_W) (c1092mo_unit 10) in
  let cut10 =
    let th = REWRITE_RULE[c1092wc_ctx] (ASSUME C1092MO_CTX) in
    let th = REWRITE_RULE[ARITH; c1092mmpe_mmmp; c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
                c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] (SPEC `2` th) in
    let th = CONV_RULE C1092MO_CODE_CONV (REWRITE_RULE (Array.to_list C1092WC_WALL_ELS) th) in
    let th = CONJUNCT1 th in
    MP (prove(mk_imp(concl th, mk_binop `(<=):real->real->bool` `&2` (list_mk_comb(`lcy`, o10))),
              REWRITE_TAC[lcy] THEN REAL_ARITH_TAC)) th in
  let box10 = REWRITE_RULE[lcont] (c1092mo_box 10) in
  let tE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`] in
  let tC = [`cE:real`; `--sE`; `vE:real`; `uE:real`; `l:real`] in
  let tA = [`cE:real`; `sE:real`; `uE + &2 * cE + &2 * sE`; `vE + &2 * cE - &2 * sE`; `l:real`] in
  let insC = SPECL tE C1092MRF_INSIDE_C and insA = SPECL tE C1092MRF_INSIDE_A in
  let tR, eqR = c1092mo_layers 9 [C1092MO_Y; C1092MO_SW] in
  let facts = [CONJUNCT1 bottom; CONJUNCT2 bottom; lower; near; tip10;
               c1092mo_seed 5 (`&47 / &20`, `&33 / &20`); c1092mo_seed 10 (`&1543 / &500`, `&2`);
               c1092mo_seed 9 (`&2`, `&457 / &500`);
               c1092mo_excl 5 7 nwc; c1092mo_excl 5 10 lower; c1092mo_excl 5 9 (CONJUNCT1 bottom);
               c1092mo_excl 5 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
               c1092mo_side (); c1092mo_pos (); MP (SPECL C1092MMPE_V OO_SIDE_LE) (ASSUME C1092MO_NP)] in
  let shift = REAL_ARITH `forall x y:real. &2 + (y - &2) = y /\ &2 - (x - &2) = &4 - x` in
  (* the inward missing profile of C *)
  SUBGOAL_THEN (list_mk_comb(`C1092IMP_profile`, tC)) MP_TAC THENL
   [MATCH_MP_TAC C1092IMP_PROFILE THEN REWRITE_TAC[insC] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC facts THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[C1092IMP_profile; REAL_NEG_NEG] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092MRF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= C1092WPS_half cE sE` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LE_DIV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* the mixed wide crossing *)
  MP_TAC(SPECL (tC @ tW @ [`cE:real`; `sE:real`; `C1092WPS_half cE sE`]) C1092MWC_POINT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ldisj; insC; insW; centerW] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC facts THEN
    REWRITE_TAC[REWRITE_RULE[ldisj] (c1092mo_apart 5 10)] THEN
    MP_TAC(c1092mo_unit 10) THEN MP_TAC cut10 THEN
    SUBGOAL_THEN (mk_forall(`x:real`, mk_forall(`y:real`,
       mk_imp(c1092mo_in 10 `&2 + x` `&2 - y`, `x <= &2`)))) (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box10) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[insC] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN (c1092mo_in 5 `&53 / &20` `&33 / &20`) ASSUME_TAC THENL
   [UNDISCH_TAC (list_mk_comb(`linside`, tC @ [`&13 / &20`; `&7 / &20`])) THEN
    REWRITE_TAC[insC] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* the inward crossing conflict *)
  MATCH_MP_TAC (SPECL (tA @ tR @ [`C1092WPS_half cE sE`]) C1092ICC_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj; insA] THEN CONV_TAC (c1092mo_conv eqR) THEN ASM_REWRITE_TAC[shift] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC (facts @ [c1092mo_punit 9 tR; c1092mo_plcont 9 [C1092MO_Y; C1092MO_SW];
                            REWRITE_RULE[ldisj] (c1092mo_apart 5 9)]) THEN
  RASM_ARITH_TAC);;

(* Lean: point *)
let C1092MRF_POINT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 10 "&3" "&12 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MRIA_RIGHT_MISSING_INNER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC (parse_term C1092MRF_LOWER) THENL
   [MATCH_MP_TAC C1092MRF_UPPER_OF_LOWER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MP (SPECL C1092MMPE_V C1092AC_RIGHT_G_COVER)
    (CONJ (ASSUME C1092MO_NP) (ASSUME C1092MO_IMG))) THEN
  ASM_REWRITE_TAC[]);;
