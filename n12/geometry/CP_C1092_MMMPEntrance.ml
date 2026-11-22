(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMPEntrance.lean                        *)
(* (N12Compact.C1092MMMPEntrance).  Universal original MMMP core ownership.  *)
(* Conventions of CP_C1092_MMMMEntrance.ml: owners p i is the OriginalOwners *)
(* 5-tuple at mask EL i c1092wc_code (side l); WallContext p mmmp is         *)
(* c1092wc_ctx c1 c2 a b l c1092mmpe_mmmp, mmmp = ![false,false,false,true]  *)
(* is c1092mmpe_mmmp (k <=> k = 3; only k < 4 matters).  Covers C1092AC_*,   *)
(* ActualEntrance.northwest_pair C1092AE_NORTHWEST_PAIR, C1092MixedSpan /    *)
(* C1092CornerTwoGaps.impossible C1092MS_IMPOSSIBLE / C1092CTG_IMPOSSIBLE,   *)
(* pullSwap / pullX by LINSIDE_PULLSW / LINSIDE_PULLX.  Tag C1092MMPE_.      *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMMEntrance.ml";;

(* Lean: mmmp *)
let c1092mmpe_mmmp = new_definition `c1092mmpe_mmmp (k:num) <=> k = 3`;;

let C1092MMPE_V = C1092MMEN_V;;
let C1092MMPE_CTX = "c1092wc_ctx c1 c2 a b l c1092mmpe_mmmp";;
let c1092mmpe_in = c1092mmen_in;;
let c1092mmpe_stmt i x y = parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s"
  C1092AE_P C1092AE_HYP C1092MMPE_CTX (c1092mmpe_in i x y));;

(* Lean: side_gt (private) *)
let C1092MMPE_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  REWRITE_TAC[OO_SIDE]);;

(* Lean: wall_auxiliaries *)
let C1092MMPE_WALL_AUXILIARIES = prove
 (parse_term (Printf.sprintf "!%s. NPACK %s /\\ %s ==> %s /\\ %s /\\ %s /\\ %s" C1092AE_P C1092AE_P
    C1092MMPE_CTX (c1092mmpe_in 8 "&1" "&113 / &50") (c1092mmpe_in 9 "&113 / &50" "&1")
    (c1092mmpe_in 10 "&3" "&113 / &50") (c1092mmpe_in 11 "&87 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; mk_small_numeral k])
    C1092WC_WALL_AUXILIARY_POINT)) [0; 1; 2; 3] THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* Lean: northwest_pair *)
let C1092MMPE_NORTHWEST_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 7 "&2" "&113 / &50") (c1092mmpe_in 7 "&87 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`]) C1092AE_NORTHWEST_PAIR) THEN
  ASM_REWRITE_TAC[c1092mmpe_mmmp; ARITH]);;

let c1092mmpe_close_tac thms pairs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC th) thms THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun (i, j) -> MP_TAC(SPECL (C1092MMPE_V @ [mk_small_numeral i; mk_small_numeral j])
    C1092WC_OWNERS_DISJOINT)) pairs THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN MESON_TAC[];;

let C1092MMPE_WA = SPEC_ALL C1092MMPE_WALL_AUXILIARIES;;
let C1092MMPE_NW = SPEC_ALL C1092MMPE_NORTHWEST_PAIR;;

(* Lean: northeast_f *)
let C1092MMPE_NORTHEAST_F = prove
 (c1092mmpe_stmt 6 "&12 / &5" "&3",
  c1092mmpe_close_tac [C1092MMPE_WA; C1092MMPE_NW; SPEC_ALL C1092AC_NORTHEAST_F_COVER]
    [6, 7; 6, 10]);;

(* Lean: top_pair *)
let C1092MMPE_TOP_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 11 "&8 / &5" "&3") (c1092mmpe_in 11 "&87 / &50" "&3")),
  c1092mmpe_close_tac [C1092MMPE_WA; C1092MMPE_NW; SPEC_ALL C1092MMPE_NORTHEAST_F;
    SPEC_ALL C1092AC_TOP_F_COVER] [11, 7; 11, 6]);;

(* local facts of northeast_pair *)
let C1092MMPE_RIGHT_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMPE_CTX (c1092mmpe_in 10 "&3" "&239 / &100")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; `2`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let C1092MMPE_CORNER2 = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092AE_HYP (c1092mmpe_in 2 "&3" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`2`]) C1092WC_CORNER_POINTS) THEN
  ASM_REWRITE_TAC[ARITH] THEN REWRITE_TAC C1092WC_LISTS);;

let C1092MMPE_OWNER6_BITS = prove
 (`10 IN bitset (EL 6 c1092wc_code)`,
  REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
  REWRITE_TAC[bitset_bits 1024; IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

let C1092MMPE_MARKER6 = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092AE_HYP
    (c1092mmpe_in 6 "&47 / &20" "&47 / &20")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`6`]) C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(MP_TAC o SPEC `10`) THEN
  REWRITE_TAC[ARITH; C1092MMPE_OWNER6_BITS; MARKER_EXPLICIT; VECTOR_2] THEN SIMP_TAC[]);;

let c1092mmpe_q k =
  let m = mk_comb(mk_comb(`EL:num->(num)list->num`, mk_small_numeral k), `c1092wc_code`) in
  map (fun f -> list_mk_comb(f, C1092MMPE_V @ [m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* pullSwap (pullX q): (s, --c, u - 4c, --(--v - a - 4s) - a, a) *)
let c1092mmpe_swx q =
  match q with [c; s; u; v; a] ->
    let neg t = mk_comb(`(--):real->real`, t)
    and sub x y = mk_binop `(-):real->real->real` x y
    and mul x y = mk_binop `( * ):real->real->real` x y in
    [s; neg c; sub u (mul `&4` c); sub (neg (sub (sub (neg v) a) (mul `&4` s))) a; a]
  | _ -> failwith "c1092mmpe_swx";;

(* Lean: northeast_pair *)
let C1092MMPE_NORTHEAST_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 6 "&12 / &5" "&3") (c1092mmpe_in 6 "&113 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th))
    [C1092MMPE_NORTHEAST_F; C1092MMPE_NORTHWEST_PAIR; C1092MMPE_WALL_AUXILIARIES;
     C1092MMPE_RIGHT_TIP; C1092MMPE_CORNER2; C1092MMPE_MARKER6; C1092AC_NORTHEAST_G_COVER] THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`EL 6 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MMPE_V C1092MMPE_SIDE_GT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY (fun j -> MP_TAC(SPECL (C1092MMPE_V @ [`6`; mk_small_numeral j])
    C1092WC_OWNERS_DISJOINT)) [7; 10; 2] THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (parse_term (c1092mmpe_in 6 "&113 / &50" "&3")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_neg(parse_term (c1092mmpe_in 6 "&3" "&12 / &5"))) ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C1092CTG_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC (c1092mmpe_q 6 @ [`&13 / &50`; `&39 / &100`]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_disj(concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092MS_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC (c1092mmpe_swx (c1092mmpe_q 6)) THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN REWRITE_TAC[LINSIDE_PULLX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

(* Lean: northeast_no_both *)
let C1092MMPE_NORTHEAST_NO_BOTH = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ~(%s /\\ %s)" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 6 "&113 / &50" "&2") (c1092mmpe_in 6 "&3" "&12 / &5")),
  c1092mmpe_close_tac [C1092MMPE_WA; SPEC_ALL C1092AC_RIGHT_G_COVER;
    SPEC_ALL C1092AC_SOUTHEAST_G_COVER] [10, 6; 5, 9; 5, 6; 5, 10]);;
