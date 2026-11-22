(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMEntrance.lean                        *)
(* (N12Compact.C1092MMMMEntrance).  The actual MMMM compulsory auxiliary    *)
(* pairs.  Conventions of C1092WallCycle.ml / ActualEntrance.ml: owners p i  *)
(* is the OriginalOwners 5-tuple at mask EL i c1092wc_code (side l); a       *)
(* WallBranch is br : num->bool (only k < 4 matters), WallContext p b is     *)
(* c1092wc_ctx c1 c2 a b l br; mmmm = ![false,false,false,false] is          *)
(* c1092mmen_mmmm (constantly F).  Covers: C1092AuxiliaryCover.ml (C1092AC_),*)
(* incoming pairs: ActualEntrance.ml (C1092AE_), C1092MixedSpan.impossible = *)
(* C1092MS_IMPOSSIBLE, C1092CornerTwoGaps.impossible = C1092CTG_IMPOSSIBLE,  *)
(* pullY = LINSIDE_PULLY.  Tag C1092MMEN_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/C1092AuxiliaryCover.ml";;
needs "n12/geometry/CP_C1092_ActualEntrance.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_C1092_CornerTwoGaps.ml";;

(* Lean: mmmm *)
let c1092mmen_mmmm = new_definition `c1092mmen_mmmm (k:num) <=> false`;;

let C1092MMEN_V = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C1092MMEN_CTX = "c1092wc_ctx c1 c2 a b l c1092mmen_mmmm";;
let c1092mmen_in i x y = c1092ae_in C1092AE_P i x y;;

(* Lean: side_gt (private) *)
let C1092MMEN_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  REWRITE_TAC[OO_SIDE]);;

(* Lean: southeast_f_cover *)
let C1092MMEN_SOUTHEAST_F_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(true,true,false)` 5
  [`&2`, `&87 / &50`; `&12 / &5`, `&1`; `&3`, `&87 / &50`];;

(* Lean: southwest_high_wall_points *)
let C1092MMEN_SOUTHWEST_HIGH_WALL_POINTS = prove
 (parse_term (Printf.sprintf "!%s. NPACK %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_P C1092MMEN_CTX
    (c1092mmen_in 8 "&1" "&113 / &50") (c1092mmen_in 9 "&113 / &50" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(SPECL (C1092MMEN_V @ [`c1092mmen_mmmm`; mk_small_numeral k])
    C1092WC_WALL_AUXILIARY_POINT)) [0; 1] THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmen_mmmm; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* the facts used by the case splits: incoming pairs, wall points, covers, disjointness *)
let c1092mmen_close_tac thms pairs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC th) thms THEN
  ASM_REWRITE_TAC[c1092mmen_mmmm] THEN
  MAP_EVERY (fun (i, j) -> MP_TAC(SPECL (C1092MMEN_V @ [mk_small_numeral i; mk_small_numeral j])
    C1092WC_OWNERS_DISJOINT)) pairs THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN MESON_TAC[];;

let C1092MMEN_NE = SPECL (C1092MMEN_V @ [`c1092mmen_mmmm`]) C1092AE_NORTHEAST_PAIR;;
let C1092MMEN_WP = SPEC_ALL C1092MMEN_SOUTHWEST_HIGH_WALL_POINTS;;
let c1092mmen_stmt i x y = parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s"
  C1092AE_P C1092AE_HYP C1092MMEN_CTX (c1092mmen_in i x y));;

(* Lean: southeast_g *)
let C1092MMEN_SOUTHEAST_G = prove
 (c1092mmen_stmt 5 "&3" "&8 / &5",
  c1092mmen_close_tac [C1092MMEN_NE; C1092MMEN_WP; SPEC_ALL C1092AC_SOUTHEAST_G_COVER]
    [5, 9; 5, 6]);;

(* Lean: northwest_f *)
let C1092MMEN_NORTHWEST_F = prove
 (c1092mmen_stmt 7 "&8 / &5" "&3",
  c1092mmen_close_tac [C1092MMEN_NE; C1092MMEN_WP; SPEC_ALL C1092AC_NORTHWEST_F_COVER]
    [7, 8; 7, 6]);;

(* Lean: right_g *)
let C1092MMEN_RIGHT_G = prove
 (c1092mmen_stmt 10 "&3" "&12 / &5",
  c1092mmen_close_tac [C1092MMEN_NE; SPEC_ALL C1092MMEN_SOUTHEAST_G;
    SPEC_ALL C1092AC_RIGHT_G_COVER] [10, 6; 10, 5]);;

(* Lean: top_f *)
let C1092MMEN_TOP_F = prove
 (c1092mmen_stmt 11 "&12 / &5" "&3",
  c1092mmen_close_tac [C1092MMEN_NE; SPEC_ALL C1092MMEN_NORTHWEST_F;
    SPEC_ALL C1092AC_TOP_F_COVER] [11, 7; 11, 6]);;

(* owners p 5 owns marker 9 *)
let C1092MMEN_OWNER5_BITS = prove
 (`9 IN bitset (EL 5 c1092wc_code)`,
  REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
  REWRITE_TAC[bitset_bits 512; IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

let C1092MMEN_MARKER = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092AE_HYP
    (c1092mmen_in 5 "&47 / &20" "&33 / &20")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMEN_V @ [`5`]) C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(MP_TAC o SPEC `9`) THEN
  REWRITE_TAC[ARITH; C1092MMEN_OWNER5_BITS; MARKER_EXPLICIT; VECTOR_2] THEN SIMP_TAC[]);;

let C1092MMEN_CORNER1 = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092AE_HYP (c1092mmen_in 1 "&3" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMEN_V @ [`1`]) C1092WC_CORNER_POINTS) THEN
  ASM_REWRITE_TAC[ARITH] THEN REWRITE_TAC C1092WC_LISTS);;

let C1092MMEN_BOTTOM_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMEN_CTX (c1092mmen_in 9 "&239 / &100" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMEN_V @ [`c1092mmen_mmmm`; `1`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmen_mmmm; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let c1092mmen_q5 =
  let m = `EL 5 c1092wc_code` in
  map (fun f -> list_mk_comb(f, C1092MMEN_V @ [m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1092mmen_pully q =
  match q with [c; s; u; v; a] ->
    [c; mk_comb(`(--):real->real`, s);
     mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` s);
     mk_binop `(-):real->real->real`
       (mk_binop `(-):real->real->real` (mk_binop `( * ):real->real->real` `&4` c) v) a; a]
  | _ -> failwith "c1092mmen_pully";;

(* Lean: southeast_pair *)
let C1092MMEN_SOUTHEAST_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMEN_CTX
    (c1092mmen_in 5 "&3" "&87 / &50") (c1092mmen_in 5 "&3" "&8 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th))
    [C1092MMEN_SOUTHEAST_G; C1092MMEN_MARKER; C1092MMEN_CORNER1; C1092MMEN_BOTTOM_TIP;
     C1092MMEN_SOUTHWEST_HIGH_WALL_POINTS; C1092MMEN_SOUTHEAST_F_COVER] THEN
  MP_TAC C1092MMEN_NE THEN
  MP_TAC(SPECL (C1092MMEN_V @ [`EL 5 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MMEN_V C1092MMEN_SIDE_GT) THEN
  ASM_REWRITE_TAC[c1092mmen_mmmm] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY (fun j -> MP_TAC(SPECL (C1092MMEN_V @ [`5`; mk_small_numeral j])
    C1092WC_OWNERS_DISJOINT)) [6; 9; 1] THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (parse_term (c1092mmen_in 5 "&3" "&87 / &50")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_neg(parse_term (c1092mmen_in 5 "&12 / &5" "&1"))) ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C1092CTG_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC (c1092mmen_pully c1092mmen_q5 @ [`&39 / &100`; `&13 / &50`]) THEN
    REWRITE_TAC[LINSIDE_PULLY; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_disj(concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092MS_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC c1092mmen_q5 THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

let C1092MMEN_CTX_CONG = prove
 (`forall c1 c2 a b l br br'. (forall k. k < 4 ==> br k = br' k) /\ c1092wc_ctx c1 c2 a b l br
     ==> c1092wc_ctx c1 c2 a b l br'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[c1092wc_ctx]) THEN ASM_SIMP_TAC[]);;

(* Lean: action (local fact of northwest_pair) *)
let C1092MMEN_ACTION = prove
 (`forall k. k < 4 ==> c1092ws_branch_action (true,false,false) c1092mmen_mmmm k = c1092mmen_mmmm k`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN CONV_TAC c1092ae_act_conv THEN
  REWRITE_TAC[c1092mmen_mmmm]);;

(* Lean: northwest_pair *)
let C1092MMEN_NORTHWEST_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMEN_CTX
    (c1092mmen_in 7 "&8 / &5" "&3") (c1092mmen_in 7 "&87 / &50" "&3")),
  let g = `(true,false,false)` and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists d1 d2 e1 e2. c1092ot_pk (true,false,false) (c1,c2,a,b) = (d1,d2,e1,e2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092wc_ctx d1 d2 e1 e2 l c1092mmen_mmmm` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
    EXISTS_TAC `c1092ws_branch_action (true,false,false) c1092mmen_mmmm` THEN
    REWRITE_TAC[C1092MMEN_ACTION] THEN
    MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]
    C1092MMEN_SOUTHEAST_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL ([g] @ v4 @ [`l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`;
                 `5`]) C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), `5`))] THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;
