(* ========================================================================= *)
(* Phase 2: Compact/Completion/C1092/OppositePair.lean                       *)
(* (N12Compact.C1092OppositePair).  The original opposite-pair BranchEnding: *)
(* its two actual central owners (owners 4 and 6) are forced to contain the *)
(* same strict centre point (2,2).                                           *)
(* Conventions of C1092WallCycle.ml / C1092WallSymmetry.ml /                 *)
(* CP_C1092_ActualEntrance.ml: owners p i is the OriginalOwners 5-tuple at   *)
(* mask EL i c1092wc_code (side l); WallContext p b is c1092wc_ctx .. br,    *)
(* `b k = false` is ~br k; BranchEnding k is c1092wsy_ending k.              *)
(* southwest_center is proved, as in Lean, by applying northeast_center to   *)
(* the half-turn g = <false,true,true> of the packing (c1092ot_pk).          *)
(* Tag C1092OP_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_ActualEntrance.ml";;
needs "n12/geometry/CP_C1092_ShortWallCenter.ml";;

let C1092OP_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* membership facts of the owner codes used below *)
let C1092OP_BITS = prove
 (`10 IN bitset (EL 6 c1092wc_code) /\ ~(9 IN bitset (EL 6 c1092wc_code)) /\
   ~(11 IN bitset (EL 6 c1092wc_code)) /\ 14 IN bitset (EL 10 c1092wc_code) /\
   15 IN bitset (EL 11 c1092wc_code)`,
  REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
  REWRITE_TAC[bitset_bits 1024; bitset_bits 16384; bitset_bits 32768; IN_SET_OF_LIST; MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* owner i at marker k: linside / ~linside from the exact markers *)
let c1092op_marker_tac i k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092OP_V5 @ [mk_small_numeral i]) C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(MP_TAC o SPEC (mk_small_numeral k)) THEN
  REWRITE_TAC[ARITH; C1092OP_BITS; MARKER_EXPLICIT; VECTOR_2] THEN SIMP_TAC[];;

let c1092op_marker i (x, y) neg k =
  prove(parse_term (Printf.sprintf "!%s. %s ==> %s%s" C1092AE_P C1092AE_HYP
                      (if neg then "~" else "") (c1092ae_in C1092AE_P i x y)),
        c1092op_marker_tac i k);;

let C1092OP_M = c1092op_marker 6 ("&47 / &20", "&47 / &20") false 10;;
let C1092OP_G = c1092op_marker 6 ("&47 / &20", "&33 / &20") true 9;;
let C1092OP_NW = c1092op_marker 6 ("&33 / &20", "&47 / &20") true 11;;
let C1092OP_RMARKER = c1092op_marker 10 ("&1543 / &500", "&2") false 14;;
let C1092OP_TMARKER = c1092op_marker 11 ("&2", "&1543 / &500") false 15;;

(* the wall frames 2 and 3 have the centre y of owner 10 and the centre x of owner 11 *)
let C1092OP_FRAME_CENTRES = prove
 (parse_term (Printf.sprintf
   "!%s. lcy (c1092wc_wfc c1 c2 a b l 2) (c1092wc_wfs c1 c2 a b l 2) (c1092wc_wfu c1 c2 a b l 2) (c1092wc_wfv c1 c2 a b l 2) l = lcy %s /\\
         lcy (c1092wc_wfc c1 c2 a b l 3) (c1092wc_wfs c1 c2 a b l 3) (c1092wc_wfu c1 c2 a b l 3) (c1092wc_wfv c1 c2 a b l 3) l = lcx %s"
   C1092AE_P (c1092ae_own C1092AE_P 10) (c1092ae_own C1092AE_P 11)),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: northeast_center *)
let C1092OP_NORTHEAST_CENTER = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ ~br 2 /\\ ~br 3 ==> %s"
   C1092AE_P C1092AE_HYP (c1092ae_in C1092AE_P 6 "&2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092OP_V5 @ [`br:num->bool`]) C1092AE_NORTHEAST_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* rHigh, tHigh: the forced points (hb k).2 10 of walls 2 and 3 *)
  MAP_EVERY (fun k -> MP_TAC(SPECL (C1092OP_V5 @ [`br:num->bool`; mk_small_numeral k; `10`])
                        C1092WC_CTX_POINT)) [2; 3] THEN
  ASM_REWRITE_TAC[ARITH; c1092wc_fpx; c1092wc_fpy; c1092wc_pmx; c1092wc_pmy; c1092wc_by] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN
  REWRITE_TAC[c1092wp_targetX; c1092wp_targetY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  (* rCut, tCut: (hb k).1 *)
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `2` (REWRITE_RULE[c1092wc_ctx] th)) THEN
                        MP_TAC(SPEC `3` (REWRITE_RULE[c1092wc_ctx] th))) THEN
  ASM_REWRITE_TAC[ARITH; C1092OP_FRAME_CENTRES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SPECL (List.concat (map (fun i -> map (fun s -> parse_term s)
      (let m = Printf.sprintf "(EL %d c1092wc_code)" i in
       map (fun f -> Printf.sprintf "%s c1 c2 a b l %s" f m) ["ooc"; "oos"; "oou"; "oov"] @ ["l:real"]))
      [6; 10; 11])) C1092SWCE_POINT) THEN
  MP_TAC(SPECL C1092OP_V5 OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[OO_UNIT; OO_BOX; C1092OP_M; C1092OP_G; C1092OP_NW; C1092OP_RMARKER; C1092OP_TMARKER;
               REAL_ARITH `&1 < l ==> &0 < l`] THEN
  CONJ_TAC THEN MATCH_MP_TAC C1092WC_OWNERS_DISJOINT THEN ASM_REWRITE_TAC[ARITH]);;

(* Lean: southwest_center *)
let C1092OP_SOUTHWEST_CENTER = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ br 0 /\\ br 1 ==> %s"
   C1092AE_P C1092AE_HYP (c1092ae_in C1092AE_P 4 "&2" "&2")),
  let g = `(false,true,true)` and pk = `c1092ot_pk`
  and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_exists(`d1:num->real`, list_mk_exists([`d2:num->real`; `e1:num->real`; `e2:num->real`],
     mk_eq(list_mk_comb(pk, [g; `(c1:num->real,c2:num->real,a:num->real,b:num->real)`]),
           `(d1:num->real,d2:num->real,e1:num->real,e2:num->real)`))))
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(`c1092wc_ctx d1 d2 e1 e2 l`,
                        mk_comb(mk_comb(`c1092ws_branch_action`, g), `br:num->bool`))) ASSUME_TAC THENL
   [MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`;
                mk_comb(mk_comb(`c1092ws_branch_action`, g), `br:num->bool`)] C1092OP_NORTHEAST_CENTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC c1092ae_act_conv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([g] @ v4 @ [`l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`;
                 `6`]) C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), `6`))] THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* Lean: oppositePair *)
let C1092OP_OPPOSITE_PAIR = prove
 (`c1092wsy_ending 3`,
  REWRITE_TAC[c1092wsy_ending] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092OP_V5 @ [`c1092ws_canonical_branch 3`]) C1092OP_SOUTHWEST_CENTER) THEN
  MP_TAC(SPECL (C1092OP_V5 @ [`c1092ws_canonical_branch 3`]) C1092OP_NORTHEAST_CENTER) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092ws_canonical_branch] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL (C1092OP_V5 @ [`4`; `6`]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN MESON_TAC[]);;
