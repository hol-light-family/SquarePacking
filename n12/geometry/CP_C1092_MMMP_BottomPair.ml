(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomPair.lean                     *)
(* (N12Compact.C1092MMMPBottomPair).  The original MMMP bottom ordinary pair.*)
(* Conventions of CP_C1092_MMMP_PointCore.ml / CP_C1092_MMMP_Origins.ml:     *)
(* forward toolkit c1092mo_* at literal masks; charts via c1092mo_layers.    *)
(* quarter q = (pullSwap (pullX q)).translated 2 2 is the layer list         *)
(* [X; SW; translated 2 2] (inside_quarter: q (2 - y) (2 + x), obtained by   *)
(* the conversions).  Covers: C1092AuxiliaryCover.ml (southwest_g_cover,     *)
(* left_g_cover, central/wall_cover_transported at g = (T,F,F) via           *)
(* c1092ac_concrete); C1092MixedSpan.impossible C1092MS_IMPOSSIBLE;          *)
(* WallUpperMissingReach.point WUMR_POINT; boundary_origin                   *)
(* OCWPBO_BOUNDARY_ORIGIN (c1092mo_origin); C1092MMMMEnding.impossible        *)
(* C1092MME_IMPOSSIBLE; S12.side_six_point C1092MPPE_SIDE_SIX_POINT;         *)
(* inside_segment C1092WC_INSIDE_SEGMENT.  Tag C1092MBP_.                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_PointCore.ml";;
needs "n12/geometry/CP_C1092_MMMMEnding.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;
needs "n12/geometry/C1092AuxiliaryCover.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_C1092_MPPMEntrance.ml";;

(* a theorem with hypothesis NPACK /\ IMAGE only, at literal masks *)
let c1092mbp_useh th =
  CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th) (c1092mo_hh ()));;
(* inside_segment between two point theorems of one owner, reduced *)
let c1092mbp_seg th0 th1 t =
  let le0 = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<=):real->real->bool` `&0` t))
  and le1 = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<=):real->real->bool` t `&1`)) in
  CONV_RULE REAL_RAT_REDUCE_CONV
    (MATCH_MP C1092WC_INSIDE_SEGMENT (CONJ th0 (CONJ th1 (CONJ le0 le1))));;

let C1092MBP_SW_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(true,false,false)` 4
  [`&1`, `&87 / &50`; `&8 / &5`, `&1`; `&2`, `&87 / &50`];;
let C1092MBP_WALL_COVER = c1092ac_concrete C1092AC_WALL_COVER_TRANSPORTED `(true,false,false)` 9
  [`&8 / &5`, `&1`; `&12 / &5`, `&1`; `&2`, `&87 / &50`];;

let C1092MBP_LEFT = c1092mo_in 9 `&8 / &5` `&1`;;
let c1092mbp_left_stmt concl =
  parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 9 "&8 / &5" "&1") concl);;
let C1092MBP_LEFT_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV);;

(* Lean: southwest_pair_of_bottom_left (private) *)
let C1092MBP_SOUTHWEST_PAIR_OF_BOTTOM_LEFT = prove
 (c1092mbp_left_stmt (c1092mmpe_in 4 "&1" "&87 / &50" ^ " /\\ " ^ c1092mmpe_in 4 "&1" "&8 / &5"),
  C1092MBP_LEFT_TAC THEN
  let left = ASSUME C1092MBP_LEFT in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let lower = c1092mbp_seg left (CONJUNCT1 (CONJUNCT2 wa)) `&7 / &33` in
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let gcov = c1092mbp_useh C1092AC_SOUTHWEST_G_COVER in
  let ccov = c1092mbp_useh C1092MBP_SW_COVER in
  let e49l = c1092mo_excl 4 9 lower and e47 = c1092mo_excl 4 7 (CONJUNCT2 nw)
  and e49 = c1092mo_excl 4 9 left in
  let gtm = c1092mo_in 4 `&1` `&8 / &5` in
  SUBGOAL_THEN gtm ASSUME_TAC THENL [MESON_TAC[gcov; e49l; e47]; ALL_TAC] THEN
  let g = ASSUME gtm in
  let t, eqs = c1092mo_layers 4 [C1092MO_X] in
  let hpt = c1092mo_in 4 `&2` `&87 / &50` and habs = mk_neg (c1092mo_in 4 `&1` `&87 / &50`) in
  let ms = DISCH hpt (DISCH habs (c1092mo_apply (c1092mo_conv eqs) (SPECL t C1092MS_IMPOSSIBLE)
    [c1092mo_punit 4 t; c1092mo_pos (); c1092mo_side (); g; e47; e49l; e49;
     ASSUME hpt; ASSUME habs])) in
  CONJ_TAC THENL [MESON_TAC[ccov; e49; ms]; ACCEPT_TAC g]);;

(* the right wall tip: local_wall_segment at wall 2 *)
let C1092MBP_RIGHT_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMPE_CTX (c1092mmpe_in 10 "&3" "&239 / &100")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; `2`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let c1092mbp_left_el () =
  let el = parse_term (c1092mmpe_in 9 "&8 / &5" "&1") in
  EQ_MP (SYM (C1092MO_CODE_CONV el)) (ASSUME C1092MBP_LEFT);;
let c1092mbp_useleft th =
  CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th)
    (CONJ (ASSUME C1092MO_NP) (CONJ (ASSUME C1092MO_IMG) (CONJ (ASSUME C1092MO_CTX) (c1092mbp_left_el ())))));;

(* Lean: top_origin_of_bottom_left (private) *)
let C1092MBP_TOP_ORIGIN_OF_BOTTOM_LEFT = prove
 (c1092mbp_left_stmt (c1092mmpe_in 11 "&2" "&3"),
  C1092MBP_LEFT_TAC THEN
  let sw = c1092mbp_useleft C1092MBP_SOUTHWEST_PAIR_OF_BOTTOM_LEFT in
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let top = c1092mo_use C1092MMPE_TOP_PAIR in
  let lcov = c1092mbp_useh C1092AC_LEFT_G_COVER in
  let utm = c1092mo_in 8 `&1` `&12 / &5` in
  SUBGOAL_THEN utm ASSUME_TAC THENL
   [MESON_TAC[lcov; c1092mo_excl 8 4 (CONJUNCT2 sw); c1092mo_excl 8 7 (CONJUNCT2 nw)]; ALL_TAC] THEN
  let upper = ASSUME utm in
  let far = c1092mo_apply ALL_CONV (SPECL (c1092mo_own 8) WUMR_POINT)
    [c1092mo_unit 8; c1092mo_pos (); c1092mo_side (); c1092mo_box 8;
     c1092mo_seed 8 (`&457 / &500`, `&2`); upper;
     c1092mo_excl 8 4 (CONJUNCT1 sw); c1092mo_excl 8 7 (c1092mo_seed 7 (`&33 / &20`, `&47 / &20`))] in
  let half = c1092mbp_seg upper far `&5 / &8` in
  let th = c1092mo_origin [C1092MO_Y] 11 3 `&457 / &500` `&8 / &5`
    [c1092mo_seed 11 (`&2`, `&1543 / &500`); CONJUNCT1 top;
     c1092mo_seed 3 (`&1`, `&1543 / &500`); c1092mo_seed 3 (`&1`, `&3`);
     c1092mo_excl 3 8 half]
    [`x:real`; `&4 - y`] in
  ACCEPT_TAC th);;

(* Lean: missing_left *)
let C1092MBP_MISSING_LEFT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ~%s"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX (c1092mmpe_in 9 "&8 / &5" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN DISCH_TAC THEN
  let left = ASSUME C1092MBP_LEFT in
  let sw = c1092mbp_useleft C1092MBP_SOUTHWEST_PAIR_OF_BOTTOM_LEFT in
  let topo = c1092mbp_useleft C1092MBP_TOP_ORIGIN_OF_BOTTOM_LEFT in
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let center = c1092mo_use C1092MPC_NORTHWEST_CENTER and north = c1092mo_use C1092MPC_NORTHWEST_NORTH
  and nleft = c1092mo_use C1092MO_NORTHWEST_LEFT in
  let rtip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MBP_RIGHT_TIP)) in
  let btip = c1092mbp_seg left (CONJUNCT1 (CONJUNCT2 wa)) `&1 / &66` in
  let ntip = c1092mbp_seg center north `&39 / &50` in
  let ltip = c1092mbp_seg nleft center `&11 / &50` in
  let q = [C1092MO_X; C1092MO_SW; c1092mo_tr `&2` `&2`] in
  let tN, eqN = c1092mo_layers 7 q and tE, eqE = c1092mo_layers 6 q and tW, eqW = c1092mo_layers 4 q in
  let facts = [c1092mo_punit 7 tN; c1092mo_punit 6 tE; c1092mo_punit 4 tW; c1092mo_pos (); c1092mo_side ();
               center; north; nleft; c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
               c1092mo_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT2 ne; CONJUNCT1 ne;
               c1092mo_seed 4 (`&33 / &20`, `&33 / &20`); CONJUNCT1 sw; CONJUNCT2 sw;
               c1092mo_excl 6 2 (c1092mo_seed 2 (`&3`, `&3`)); c1092mo_excl 6 11 topo;
               c1092mo_excl 6 10 rtip; c1092mo_excl 6 7 ntip;
               c1092mo_excl 4 0 (c1092mo_seed 0 (`&1`, `&1`));
               c1092mo_excl 4 8 (c1092mo_use C1092MO_LEFT_ORIGIN);
               c1092mo_excl 4 9 btip; c1092mo_excl 4 7 ltip;
               c1092mo_apart 7 6; c1092mo_apart 7 4] in
  MATCH_MP_TAC (SPECL (tN @ tE @ tW) C1092MME_IMPOSSIBLE) THEN
  REWRITE_TAC[c1092mme_data; ldisj] THEN CONV_TAC (c1092mo_conv (eqN @ eqE @ eqW)) THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

(* Lean: pair *)
let C1092MBP_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 9 "&12 / &5" "&1") (c1092mmpe_in 9 "&113 / &50" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let bottom = CONJUNCT1 (CONJUNCT2 wa) in
  let omitted = c1092mo_use C1092MBP_MISSING_LEFT in
  let wcov = c1092mbp_useh C1092MBP_WALL_COVER in
  let t, eqs = c1092mo_layers 9 [C1092MO_X; C1092MO_SW] in
  let hpt = c1092mo_in 9 `&2` `&87 / &50` in
  let six = DISCH hpt (c1092mo_apply (c1092mo_conv eqs) (SPECL t C1092MPPE_SIDE_SIX_POINT)
    [c1092mo_punit 9 t; c1092mo_side (); c1092mo_seed 9 (`&2`, `&457 / &500`); bottom; ASSUME hpt]) in
  let e95 = c1092mo_excl 9 5 (c1092mo_seed 5 (`&47 / &20`, `&33 / &20`)) in
  CONJ_TAC THENL [MESON_TAC[wcov; omitted; six; e95]; ACCEPT_TAC bottom]);;
