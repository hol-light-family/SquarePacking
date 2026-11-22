(* ========================================================================= *)
(* Phase 2: Compact/Completion/C1092/ActualEntrance.lean                     *)
(* (N12Compact.C1092ActualEntrance).  Actual C1092 incoming wall pairs.      *)
(* Conventions of C1092WallCycle.ml / C1092WallSymmetry.ml: owners p i is    *)
(* the OriginalOwners 5-tuple at mask EL i c1092wc_code (side l); a          *)
(* WallBranch is br : num->bool, WallContext p b is c1092wc_ctx c1 c2 a b l  *)
(* br; the transformed packing g.pullPacking p is (d1,d2,e1,e2) with        *)
(* c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2); canonicalBranch k is           *)
(* c1092ws_canonical_branch k.  Tag C1092AE_.                                *)
(* ========================================================================= *)

needs "n12/geometry/C1092WallSymmetry.ml";;
needs "n12/geometry/CP_C1092_InwardElbows.ml";;

let c1092ae_own pk i =
  let m = Printf.sprintf "(EL %d c1092wc_code)" i in
  Printf.sprintf "(ooc %s %s) (oos %s %s) (oou %s %s) (oov %s %s) l" pk m pk m pk m pk m;;
let c1092ae_in pk i x y = Printf.sprintf "linside %s (%s) (%s)" (c1092ae_own pk i) x y;;
let C1092AE_P = "c1 c2 a b l";;
let C1092AE_HYP =
  "NPACK c1 c2 a b l /\\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family";;

(* evaluates the actions (branch, wall, owner) at literal transforms *)
let c1092ae_act_conv =
  REWRITE_CONV[c1092ws_branch_action; c1092ws_wall_flip; c1092ws_wall_action;
               c1092ws_owner_action; LET_DEF; LET_END_DEF] THENC
  REWRITE_CONV (C1092WS_LOOKUPS) THENC ONCE_DEPTH_CONV EL_CONV THENC REWRITE_CONV[];;

let C1092AE_OWNER4_BITS = prove
 (`8 IN bitset (EL 4 c1092wc_code) /\ ~(9 IN bitset (EL 4 c1092wc_code)) /\
   ~(11 IN bitset (EL 4 c1092wc_code))`,
  REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
  REWRITE_TAC[bitset_bits 256; IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

let c1092ae_marker_tac k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `4`]
    C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(MP_TAC o SPEC (mk_small_numeral k)) THEN
  REWRITE_TAC[ARITH; C1092AE_OWNER4_BITS; MARKER_EXPLICIT; VECTOR_2] THEN SIMP_TAC[];;

(* Lean: southwest_marker *)
let C1092AE_SOUTHWEST_MARKER = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092AE_HYP
    (c1092ae_in C1092AE_P 4 "&33 / &20" "&33 / &20")),
  c1092ae_marker_tac 8);;

(* Lean: southwest_missing_east *)
let C1092AE_SOUTHWEST_MISSING_EAST = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ~%s" C1092AE_P C1092AE_HYP
    (c1092ae_in C1092AE_P 4 "&47 / &20" "&33 / &20")),
  c1092ae_marker_tac 9);;

(* Lean: southwest_missing_north *)
let C1092AE_SOUTHWEST_MISSING_NORTH = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ~%s" C1092AE_P C1092AE_HYP
    (c1092ae_in C1092AE_P 4 "&33 / &20" "&47 / &20")),
  c1092ae_marker_tac 11);;

let c1092ae_pair_concl pk i (x1, y1) (x2, y2) =
  Printf.sprintf "%s /\\ %s" (c1092ae_in pk i x1 y1) (c1092ae_in pk i x2 y2);;

(* Lean: southwest_pair *)
let C1092AE_SOUTHWEST_PAIR = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ br 0 /\\ br 1 ==> %s"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 4 ("&2", "&87 / &50") ("&87 / &50", "&2"))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
      `l:real`; `br:num->bool`; mk_small_numeral k; `&803 / &500`] C1092WC_LOCAL_WALL_SEGMENT) THEN
      MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
      `l:real`; `br:num->bool`; mk_small_numeral k] C1092WC_WALL_AUXILIARY_POINT)) [0; 1] THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MAP_EVERY (fun j -> MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
      `l:real`; `4`; mk_small_numeral j] C1092WC_OWNERS_DISJOINT)) [8; 9] THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC C1092IE_PAIR THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `EL 4 c1092wc_code`] OO_UNIT) THEN
  ASM_SIMP_TAC[C1092AE_SOUTHWEST_MARKER; C1092AE_SOUTHWEST_MISSING_EAST;
               C1092AE_SOUTHWEST_MISSING_NORTH] THEN
  REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* the transported pairs: apply southwest_pair to g.pullPacking p *)
let c1092ae_transport_tac g =
  let pk = `c1092ot_pk` and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
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
                mk_comb(mk_comb(`c1092ws_branch_action`, g), `br:num->bool`)] C1092AE_SOUTHWEST_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC c1092ae_act_conv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([g] @ v4 @ [`l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`;
                 `4`]) C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), `4`))] THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];;

(* Lean: northeast_pair *)
let C1092AE_NORTHEAST_PAIR = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ ~br 2 /\\ ~br 3 ==> %s"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 6 ("&2", "&113 / &50") ("&113 / &50", "&2"))),
  c1092ae_transport_tac `(false,true,true)`);;

(* Lean: southeast_pair *)
let C1092AE_SOUTHEAST_PAIR = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ br 2 /\\ ~br 1 ==> %s"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 5 ("&2", "&87 / &50") ("&113 / &50", "&2"))),
  c1092ae_transport_tac `(false,true,false)`);;

(* Lean: northwest_pair *)
let C1092AE_NORTHWEST_PAIR = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ ~br 0 /\\ br 3 ==> %s"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 7 ("&2", "&113 / &50") ("&87 / &50", "&2"))),
  c1092ae_transport_tac `(false,false,true)`);;


(* Lean: opposite_branch_pairs *)
let C1092AE_OPPOSITE_BRANCH_PAIRS = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c1092wc_ctx c1 c2 a b l (c1092ws_canonical_branch 3) ==> (%s) /\\ (%s)"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 4 ("&2", "&87 / &50") ("&87 / &50", "&2"))
   (c1092ae_pair_concl C1092AE_P 6 ("&2", "&113 / &50") ("&113 / &50", "&2"))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC C1092AE_SOUTHWEST_PAIR; MATCH_MP_TAC C1092AE_NORTHEAST_PAIR] THEN
  EXISTS_TAC `c1092ws_canonical_branch 3` THEN
  ASM_REWRITE_TAC[c1092ws_canonical_branch] THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* Lean: exceptional_branch_pair *)
let C1092AE_EXCEPTIONAL_BRANCH_PAIR = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c1092wc_ctx c1 c2 a b l (c1092ws_canonical_branch 1) ==> %s"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 4 ("&2", "&87 / &50") ("&87 / &50", "&2"))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1092AE_SOUTHWEST_PAIR THEN
  EXISTS_TAC `c1092ws_canonical_branch 1` THEN
  ASM_REWRITE_TAC[c1092ws_canonical_branch] THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* Lean: adjacent_branch_pair *)
let C1092AE_ADJACENT_BRANCH_PAIR = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c1092wc_ctx c1 c2 a b l (c1092ws_canonical_branch 2) ==> %s"
   C1092AE_P C1092AE_HYP
   (c1092ae_pair_concl C1092AE_P 5 ("&2", "&87 / &50") ("&113 / &50", "&2"))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1092AE_SOUTHEAST_PAIR THEN
  EXISTS_TAC `c1092ws_canonical_branch 2` THEN
  ASM_REWRITE_TAC[c1092ws_canonical_branch] THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;
