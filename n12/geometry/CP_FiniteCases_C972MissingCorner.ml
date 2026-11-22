(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972MissingCorner.lean             *)
(* (namespace N12Compact.FiniteCases.C972).  C972's two genuine missing-     *)
(* corner roots (conditional branch exclusions, not an exclusion of C972).   *)
(* owners p i is the owner of mask EL i c972o_masks, written with the        *)
(* literal mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,2048,4096,  *)
(* 8192,16384).  fixed = C972CS_FIXED (c972cs_fixed / c972e_points fields),  *)
(* seed = oo_seed, foreign = oo_excl-style c972mc_excl / C972CS_CLASH_TAC,   *)
(* apart = oo_apart, side / box / cap = OO_SIDE / OO_BOX / OO_SIDE_LE,       *)
(* markers = OO_MARKERS, missing_top = oo_missing m 15.                      *)
(* SingletonMissing.zero/one_missing_points = CCSM_ZERO/ONE_MISSING_POINTS,  *)
(* C981CompletionWallAdvance.point = C981WA_POINT, vertical_segment =        *)
(* OO_VERTICAL_SEGMENT, OrdinaryMarkerHalfpoint.point_original =            *)
(* OCOMHM_POINT_ORIGINAL, WallProfile.boundary_origin = OCWPBO_BOUNDARY_     *)
(* ORIGIN, C974976Central.bottom_origin / southeast_lower / southeast_g6 /   *)
(* EndingInput = CC974O_BOTTOM_ORIGIN / CC974O_SOUTHEAST_LOWER /             *)
(* CC974C_SOUTHEAST_G6 / cc974c_ending, C983.C974LocalData.Input =          *)
(* c983ld_input (c983ld_tr / c983ld_sw tuples), C974LocalEnding.impossible = *)
(* C983LE_IMPOSSIBLE.  Tag C972MC_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972CentralSelection.ml";;
needs "n12/geometry/CP_CommonCases_C974976Origins.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryMarkerHalfpoint_Main.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

let C972MC_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C972MC_NP = `NPACK c1 c2 a b l`;;
let C972MC_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c972d_family`;;
let c972mc_np = ASSUME C972MC_NP;;
let c972mc_hh = CONJ c972mc_np (ASSUME C972MC_IMG);;
let c972mc_stmt hyps body =
  list_mk_forall(C972MC_V5, mk_imp(list_mk_conj([C972MC_NP; C972MC_IMG] @ hyps), body));;
let c972mc_tuple m =
  map (fun f -> list_mk_comb(f, C972MC_V5 @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c972mc_own m x y = list_mk_comb(`linside`, c972mc_tuple m @ [x; y]);;
let c972mc_inst th = MP (SPECL C972MC_V5 th) c972mc_hh;;
let c972mc_inst1 th h = MP (SPECL C972MC_V5 th) (CONJ c972mc_np (CONJ (ASSUME C972MC_IMG) h));;
let c972mc_seed m p = c972mc_inst (oo_inst C972D_F (oo_seed m p));;
let c972mc_apart m n = REWRITE_RULE[ldisj] (c972mc_inst (oo_apart C972D_F m n));;
let c972mc_excl m n pt =
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] (c972mc_apart m n) in
  let qa = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH qa (MP (NOT_ELIM d2) (CONJ (ASSUME qa) pt)));;
let c972mc_unit m = MP (SPECL (C972MC_V5 @ [mk_small_numeral m]) OO_UNIT) c972mc_np;;
let c972mc_box m = MP (SPECL (C972MC_V5 @ [mk_small_numeral m]) OO_BOX) c972mc_np;;
let C972MC_SIDE = MP (SPECL C972MC_V5 OO_SIDE) c972mc_np;;
let C972MC_FIXED = CONJUNCTS (REWRITE_RULE[c972cs_fixed; c972e_points] (c972mc_inst C972CS_FIXED));;
let c972mc_fixed m x y =
  let tm = c972mc_own m x y in
  try find (fun th -> concl th = tm) C972MC_FIXED with Failure _ -> failwith "c972mc_fixed";;

(* C983LE_IMPOSSIBLE at three owner tuples, from the Input theorem *)
let c972mc_close tK tW tC ms inth =
  let units = map c972mc_unit ms in
  let pos = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) C972MC_SIDE in
  let th = SPECL (tK @ tW @ tC) C983LE_IMPOSSIBLE in
  MP th (TAC_PROOF(([], lhand (concl th)),
    REPEAT CONJ_TAC THEN
    FIRST [ACCEPT_TAC pos; ACCEPT_TAC inth; MAP_EVERY MP_TAC units THEN REAL_ARITH_TAC]));;

(* the SingletonMissing hypotheses for owner m in {1, 2} (cap, markers) *)
let C972MC_SINGLETON_TAC m th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
  MP_TAC(SPECL C972MC_V5 OO_SIDE) THEN MP_TAC(SPECL C972MC_V5 OO_SIDE_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  MP_TAC(SPECL (C972MC_V5 @ [C972D_F; mk_small_numeral m]) OO_MARKERS) THEN
  ASM_REWRITE_TAC[in_fam m C972D_F] THEN
  REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM];;

(* Lean: missing_zero_points *)
let C972MC_MISSING_ZERO_POINTS = prove
 (c972mc_stmt [mk_neg (c972mc_own 1 `&1` `&1`)]
    (mk_conj(c972mc_own 1 `&91 / &50` `&1`, c972mc_own 1 `&49 / &25` `&19 / &25`)),
  C972MC_SINGLETON_TAC 1 CCSM_ZERO_MISSING_POINTS);;

(* Lean: missing_one_points *)
let C972MC_MISSING_ONE_POINTS = prove
 (c972mc_stmt [mk_neg (c972mc_own 2 `&1` `&1`)]
    (mk_conj(c972mc_own 2 `&1` `&91 / &50`, c972mc_own 2 `&19 / &25` `&49 / &25`)),
  C972MC_SINGLETON_TAC 2 CCSM_ONE_MISSING_POINTS);;

(* a lemma instance at (pulled) owner tuples: side conditions *)
let C972MC_WALL_TAC m =
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP (REWRITE_RULE[lcont]
    (UNDISCH (SPECL (C972MC_V5 @ [mk_small_numeral m]) OO_BOX)))) THEN
  REAL_ARITH_TAC;;
let C972MC_SIDE_TAC extra =
  REWRITE_TAC[REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST ([FIRST_ASSUM ACCEPT_TAC;
          ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
          DISCH_TAC THEN C972CS_CLASH_TAC;
          RASM_ARITH_TAC] @ extra);;
let C972MC_PULL_CONV =
  REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THENC
  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* Lean: left_reach *)
let C972MC_LEFT_REACH = prove
 (c972mc_stmt [] (c972mc_own 4096 `&1` `&14 / &5`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 4096 THEN
  C972CS_SV `&87 / &50` THEN
  MATCH_MP_TAC (SPECL (c972mc_tuple 4096) C981WA_POINT) THEN C972MC_SIDE_TAC []);;

(* Lean: left_bar *)
let C972MC_LEFT_BAR = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     &113 / &50 <= y /\ y <= &14 / &5
     ==> linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l (&1) (y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972MC_LEFT_REACH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: northwest_halfpoint *)
let C972MC_NORTHWEST_HALFPOINT = prove
 (c972mc_stmt [mk_neg (c972mc_own 2048 `&2` `&113 / &50`)] (c972mc_own 2048 `&3 / &2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 2048 THEN
  MATCH_MP_TAC (CONV_RULE C972MC_PULL_CONV
    (SPECL (c983ld_sw (c972mc_tuple 2048) @ [`&43 / &500`]) OCOMHM_POINT_ORIGINAL)) THEN
  C972MC_SIDE_TAC []);;

(* Lean: left_origin_of_northwest_halfpoint *)
let C972MC_LEFT_ORIGIN_OF_NORTHWEST_HALFPOINT =
  let pully t = match t with
      [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`])
                           [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`]
    | _ -> failwith "pully" in
  let pull t = c983ld_sw (pully t) in
  prove
   (c972mc_stmt [c972mc_own 2048 `&3 / &2` `&3`] (c972mc_own 4096 `&1` `&2`),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 4096 THEN C972CS_OWNER_TAC 192 THEN
    MP_TAC(SPEC_ALL (oo_inst C972D_F (oo_seed 192 (`&457 / &500`, `&3`)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC (CONV_RULE C972MC_PULL_CONV
      (SPECL (pull (c972mc_tuple 4096) @ pull (c972mc_tuple 192) @ [`&457 / &500`; `&8 / &5`])
         OCWPBO_BOUNDARY_ORIGIN)) THEN
    C972MC_SIDE_TAC
     [C972MC_WALL_TAC 4096; C972MC_WALL_TAC 192;
      REWRITE_TAC[ldisj; LINSIDE_PULLSW; LINSIDE_PULLY] THEN MP_TAC (SPEC_ALL (oo_apart C972D_F 192 4096)) THEN ASM_REWRITE_TAC[ldisj] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: left_missing_impossible *)
let C972MC_LEFT_MISSING_IMPOSSIBLE =
  let missing = mk_neg (c972mc_own 2 `&1` `&1`) and half = c972mc_own 2048 `&3 / &2` `&3` in
  let hth = ASSUME half in
  let seeds = CONJUNCTS (c972mc_inst1 C972MC_MISSING_ONE_POINTS (ASSUME missing)) in
  let facts = [C972MC_SIDE; c972mc_seed 2 (`&457 / &500`, `&1`); el 0 seeds; el 1 seeds;
               ASSUME missing; c972mc_inst1 C972MC_LEFT_ORIGIN_OF_NORTHWEST_HALFPOINT hth;
               c972mc_fixed 4096 `&457 / &500` `&2`; c972mc_inst C972MC_LEFT_REACH;
               c972mc_excl 4096 2048 (c972mc_fixed 2048 `&33 / &20` `&47 / &20`);
               c972mc_excl 4096 256 (c972mc_inst C972CS_SOUTHWEST_WEST);
               c972mc_excl 4096 2048 hth;
               c972mc_fixed 192 `&1` `&3`; c972mc_excl 192 2048 hth;
               c972mc_apart 2 4096; c972mc_apart 2 192; c972mc_apart 4096 192] in
  let tr t = c983ld_tr (c983ld_sw t) in
  let tK = tr (c972mc_tuple 2) and tW = tr (c972mc_tuple 4096) and tC = tr (c972mc_tuple 192) in
  let inth = TAC_PROOF(([], c983ld_concl tK tW tC),
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (c972mc_box 2); REWRITE_RULE[lcont] (c972mc_box 192)]) in
  let th = c972mc_close tK tW tC [2; 4096; 192] inth in
  prove(c972mc_stmt [missing; half] `false`, REPEAT GEN_TAC THEN STRIP_TAC THEN ACCEPT_TAC th);;

(* Lean: zero_corner_of_southeast_halfpoint *)
let C972MC_ZERO_CORNER_OF_SOUTHEAST_HALFPOINT =
  let missing = mk_neg (c972mc_own 1 `&1` `&1`) and half = c972mc_own 512 `&3` `&3 / &2` in
  let hth = ASSUME half in
  let seeds = CONJUNCTS (c972mc_inst1 C972MC_MISSING_ZERO_POINTS (ASSUME missing)) in
  let origin =
    let th = SPECL (c972mc_tuple 8192 @ c972mc_tuple 12 @ c972mc_tuple 512) CC974O_BOTTOM_ORIGIN in
    let ps = [c972mc_fixed 8192 `&2` `&457 / &500`; c972mc_fixed 8192 `&12 / &5` `&1`;
              c972mc_seed 12 (`&3`, `&457 / &500`); c972mc_fixed 12 `&3` `&1`; hth;
              c972mc_box 8192; c972mc_box 12;
              c972mc_inst (oo_apart C972D_F 12 512); c972mc_inst (oo_apart C972D_F 12 8192)] @
             map c972mc_unit [8192; 12; 512] in
    MP th (TAC_PROOF(([], lhand (concl th)),
      REPEAT CONJ_TAC THEN
      FIRST [FIRST (map ACCEPT_TAC ps); REFL_TAC; MP_TAC C972MC_SIDE THEN REAL_ARITH_TAC])) in
  let facts = [C972MC_SIDE; c972mc_seed 1 (`&1`, `&457 / &500`); el 0 seeds; el 1 seeds;
               ASSUME missing; origin;
               c972mc_fixed 8192 `&2` `&457 / &500`;
               CONJUNCT1 (c972mc_inst C972CS_BOTTOM_REACH);
               c972mc_excl 8192 512 (c972mc_fixed 512 `&47 / &20` `&33 / &20`);
               c972mc_excl 8192 256 (c972mc_inst C972CS_SOUTHWEST_SOUTH);
               c972mc_excl 8192 512 hth;
               c972mc_fixed 12 `&3` `&1`; c972mc_excl 12 512 hth;
               c972mc_apart 1 8192; c972mc_apart 1 12; c972mc_apart 8192 12] in
  let tK = c983ld_tr (c972mc_tuple 1) and tW = c983ld_tr (c972mc_tuple 8192)
  and tC = c983ld_tr (c972mc_tuple 12) in
  let inth = TAC_PROOF(([], c983ld_concl tK tW tC),
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (c972mc_box 1); REWRITE_RULE[lcont] (c972mc_box 12)]) in
  let th = c972mc_close tK tW tC [1; 8192; 12] inth in
  prove
   (c972mc_stmt [half] (c972mc_own 1 `&1` `&1`),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REFUTE_THEN (fun h -> ACCEPT_TAC (PROVE_HYP h th)));;

(* Lean: one_corner_of_northwest_missing_f5 *)
let C972MC_ONE_CORNER_OF_NORTHWEST_MISSING_F5 = prove
 (c972mc_stmt [mk_neg (c972mc_own 2048 `&2` `&113 / &50`)] (c972mc_own 2 `&1` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972MC_NORTHWEST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPEC_ALL C972MC_LEFT_MISSING_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: southeast_halfpoint_of_northeast_missing_origin *)
let C972MC_SOUTHEAST_HALFPOINT_OF_NORTHEAST_MISSING_ORIGIN = prove
 (c972mc_stmt [mk_neg (c972mc_own 1024 `&2` `&3`)] (c972mc_own 512 `&3` `&3 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (list_mk_comb(`cc974c_ending`, c972mc_tuple 512 @ c972mc_tuple 1024)) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C972CS_SELECTION_INPUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C972CS_FIXED_TAC THEN
    REWRITE_TAC[cc974c_ending] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(DISCH_TAC THEN C972CS_CLASH_TAC) THEN
    X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL (C972MC_V5 @ [`y:real`]) C972CS_RIGHT_BAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C972CS_CLASH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (c972mc_own 512 `&113 / &50` `&2`) ASSUME_TAC THENL
   [MATCH_MP_TAC CC974C_SOUTHEAST_G6 THEN
    MAP_EVERY EXISTS_TAC (c972mc_tuple 1024) THEN
    ASM_SIMP_TAC[OO_UNIT] THEN MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CC974O_SOUTHEAST_LOWER THEN
  MAP_EVERY EXISTS_TAC (c972mc_tuple 1024) THEN
  ASM_SIMP_TAC[OO_UNIT] THEN MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: remaining_alternative *)
let C972MC_REMAINING_ALTERNATIVE = prove
 (c972mc_stmt [] (mk_disj(c972mc_own 2048 `&2` `&113 / &50`, c972mc_own 1024 `&2` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c972mc_own 2048 `&2` `&113 / &50`) THEN ASM_REWRITE_TAC[] THEN
  REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPEC_ALL C972MC_ONE_CORNER_OF_NORTHWEST_MISSING_F5) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972MC_SOUTHEAST_HALFPOINT_OF_NORTHEAST_MISSING_ORIGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972MC_ZERO_CORNER_OF_SOUTHEAST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`&1`; `&1`] (c972mc_apart 1 2)) THEN ASM_REWRITE_TAC[]);;
