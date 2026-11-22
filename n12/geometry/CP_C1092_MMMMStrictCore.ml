(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMStrictCore.lean                      *)
(* (N12Compact.C1092MMMMStrictCore).  The MMMM entrance has its northeast    *)
(* center and both half-unit crosspoints.  Conventions of                    *)
(* CP_C1092_MMMMEntrance.ml (owners p i = OriginalOwners 5-tuple at mask     *)
(* EL i c1092wc_code, WallContext p mmmm = c1092wc_ctx .. c1092mmen_mmmm).    *)
(* CentralWallCenter.right_high CWC_RIGHT_HIGH, C981CompletionCrosspoint.    *)
(* point C981CP_POINT, C1092OppositePair.northeast_center                    *)
(* C1092OP_NORTHEAST_CENTER, p.contained OO_BOX, container_pullSwap          *)
(* LCONT_PULLSW, inside_pullSwap LINSIDE_PULLSW.  Tag C1092MMSC_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMMEntrance.ml";;
needs "n12/geometry/CP_C1092_OppositePair.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CentralWallCenter.ml";;

let C1092MMSC_V = C1092MMEN_V;;
let c1092mmsc_in = c1092mmen_in;;
let c1092mmsc_stmt concl = parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s"
  C1092AE_P C1092AE_HYP C1092MMEN_CTX concl);;

(* Lean: side_gt (private) *)
let C1092MMSC_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  REWRITE_TAC[OO_SIDE]);;

(* owners p i owns (or misses) marker k; code = EL i c1092wc_code *)
let c1092mmsc_marker pos i code k x y =
  let bt = parse_term (Printf.sprintf "%d IN bitset (EL %d c1092wc_code)" k i) in
  let bits = prove
   ((if pos then bt else mk_neg bt),
    REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
    REWRITE_TAC[bitset_bits code; IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV) in
  let lin = c1092mmsc_in i x y in
  prove
   (parse_term (Printf.sprintf "!%s. %s ==> %s%s" C1092AE_P C1092AE_HYP (if pos then "" else "~") lin),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL (C1092MMSC_V @ [mk_small_numeral i]) C1092WC_OWNERS_MARKERS) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(MP_TAC o SPEC (mk_small_numeral k)) THEN
    REWRITE_TAC[ARITH; bits; MARKER_EXPLICIT; VECTOR_2] THEN SIMP_TAC[]);;

let c1092mmsc_q i =
  let m = mk_comb(mk_comb(`EL:num->(num)list->num`, mk_small_numeral i), `c1092wc_code`) in
  map (fun f -> list_mk_comb(f, C1092MMSC_V @ [m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1092mmsc_sw q =
  match q with [c; s; u; v; a] ->
    [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c1092mmsc_sw";;

(* loads the owner facts of owner i and the disjointness with the owners js *)
let c1092mmsc_setup i ths js =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th)) ths THEN
  MP_TAC(SPECL (C1092MMSC_V @ [list_mk_comb(`EL:num->(num)list->num`,
    [mk_small_numeral i; `c1092wc_code`])]) OO_UNIT) THEN
  MP_TAC(SPECL (C1092MMSC_V @ [list_mk_comb(`EL:num->(num)list->num`,
    [mk_small_numeral i; `c1092wc_code`])]) OO_BOX) THEN
  MP_TAC(SPECL C1092MMSC_V C1092MMSC_SIDE_GT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY (fun j -> MP_TAC(SPECL (C1092MMSC_V @ [mk_small_numeral i; mk_small_numeral j])
    C1092WC_OWNERS_DISJOINT)) js THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN REPEAT DISCH_TAC;;

let C1092MMSC_MARKER10 = c1092mmsc_marker true 10 16384 14 "&1543 / &500" "&2";;
let C1092MMSC_MARKER11 = c1092mmsc_marker true 11 32768 15 "&2" "&1543 / &500";;
let C1092MMSC_MARKER6 = c1092mmsc_marker true 6 1024 10 "&47 / &20" "&47 / &20";;
let C1092MMSC_MISSING_SE = c1092mmsc_marker false 6 1024 9 "&47 / &20" "&33 / &20";;
let C1092MMSC_MISSING_NW = c1092mmsc_marker false 6 1024 11 "&33 / &20" "&47 / &20";;
let C1092MMSC_INWARD = SPECL (C1092MMSC_V @ [`c1092mmen_mmmm`]) C1092AE_NORTHEAST_PAIR;;

let c1092mmsc_close_tac =
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LCONT_PULLSW)) THEN ASM_MESON_TAC[];;

(* Lean: right_halfpoint *)
let C1092MMSC_RIGHT_HALFPOINT = prove
 (c1092mmsc_stmt (c1092mmsc_in 10 "&3" "&5 / &2"),
  c1092mmsc_setup 10 [C1092MMEN_SOUTHEAST_PAIR; C1092MMSC_MARKER10; C1092MMEN_RIGHT_G] [5; 6] THEN
  MP_TAC C1092MMSC_INWARD THEN ASM_REWRITE_TAC[c1092mmen_mmmm] THEN STRIP_TAC THEN
  MATCH_MP_TAC CWC_RIGHT_HIGH THEN ASM_REWRITE_TAC[] THEN c1092mmsc_close_tac);;

(* Lean: top_halfpoint *)
let C1092MMSC_TOP_HALFPOINT = prove
 (c1092mmsc_stmt (c1092mmsc_in 11 "&5 / &2" "&3"),
  c1092mmsc_setup 11 [C1092MMEN_NORTHWEST_PAIR; C1092MMSC_MARKER11; C1092MMEN_TOP_F] [7; 6] THEN
  MP_TAC C1092MMSC_INWARD THEN ASM_REWRITE_TAC[c1092mmen_mmmm] THEN STRIP_TAC THEN
  MP_TAC(SPECL (c1092mmsc_sw (c1092mmsc_q 11)) CWC_RIGHT_HIGH) THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN DISCH_THEN MATCH_MP_TAC THEN c1092mmsc_close_tac);;

(* Lean: northeast_halfpoints *)
let C1092MMSC_NORTHEAST_HALFPOINTS = prove
 (c1092mmsc_stmt (c1092mmsc_in 6 "&2" "&5 / &2" ^ " /\\ " ^ c1092mmsc_in 6 "&5 / &2" "&2"),
  c1092mmsc_setup 6 [C1092MMSC_MARKER6; C1092MMSC_MISSING_SE; C1092MMSC_MISSING_NW;
    C1092MMEN_RIGHT_G; C1092MMSC_RIGHT_HALFPOINT; C1092MMEN_TOP_F; C1092MMSC_TOP_HALFPOINT]
    [10; 11] THEN
  MP_TAC C1092MMSC_INWARD THEN ASM_REWRITE_TAC[c1092mmen_mmmm] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C981CP_POINT THEN ASM_REWRITE_TAC[] THEN c1092mmsc_close_tac;
    MP_TAC(SPECL (c1092mmsc_sw (c1092mmsc_q 6)) C981CP_POINT) THEN
    REWRITE_TAC[LINSIDE_PULLSW] THEN DISCH_THEN MATCH_MP_TAC THEN c1092mmsc_close_tac]);;

(* Lean: northeast_triangle *)
let C1092MMSC_NORTHEAST_TRIANGLE = prove
 (c1092mmsc_stmt (c1092mmsc_in 6 "&2" "&2" ^ " /\\ " ^ c1092mmsc_in 6 "&5 / &2" "&2" ^ " /\\ " ^
    c1092mmsc_in 6 "&2" "&5 / &2"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MMSC_NORTHEAST_HALFPOINTS) THEN
  MP_TAC(SPECL (C1092MMSC_V @ [`c1092mmen_mmmm`]) C1092OP_NORTHEAST_CENTER) THEN
  ASM_REWRITE_TAC[c1092mmen_mmmm] THEN SIMP_TAC[]);;
