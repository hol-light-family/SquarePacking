(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMEntrance.lean                        *)
(* (N12Compact.C1092MPPMEntrance).  Original MPPM wall-omission ancestry.    *)
(* Conventions of CP_C1092_MMMMEntrance.ml / CP_C1092_MMMPEntrance.ml:       *)
(* owners p i is the OriginalOwners 5-tuple at mask EL i c1092wc_code (side  *)
(* l); WallContext p mppm is c1092wc_ctx c1 c2 a b l c1092mppe_mppm, mppm =  *)
(* ![false,true,true,false] is c1092mppe_mppm (k <=> k = 1 \/ k = 2).        *)
(* S12.side_six_point (source/S12/ShortCluster/SideSixPoint.lean, not yet in *)
(* HOL) is ported locally as C1092MPPE_SIDE_SIX_POINT (short_projections is  *)
(* WFP_SHORT_PROJECTIONS).  OriginalOwners.horizontal_segment is            *)
(* OO_HORIZONTAL_SEGMENT, pullSwap / pullY are LINSIDE_PULLSW / LINSIDE_PULLY.*)
(* Tag C1092MPPE_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMMEntrance.ml";;
needs "n12/geometry/CP_C1092_MMMPEntrance.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: S12.side_six_point *)
let C1092MPPE_SIDE_SIX_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&87 / &50) /\
     linside c s u v a (&87 / &50) (&2)
     ==> linside c s u v a (&1) (&8 / &5) \/ linside c s u v a (&1) (&12 / &5) \/
         linside c s u v a (&33 / &20) (&33 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (dx, dy) ->
    MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC])
    [`&0`, `--(&4 / &5)`; `--(&13 / &20)`, `--(&1 / &20)`; `--(&13 / &20)`, `&3 / &4`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q /\ ~r ==> false) ==> p \/ q \/ r`) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM; REAL_NOT_LT]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: mppm *)
let c1092mppe_mppm = new_definition `c1092mppe_mppm (k:num) <=> k = 1 \/ k = 2`;;

let C1092MPPE_V = C1092MMEN_V;;
let C1092MPPE_CTX = "c1092wc_ctx c1 c2 a b l c1092mppe_mppm";;
let c1092mppe_in = c1092mmen_in;;
let C1092MPPE_OMIT = "~" ^ c1092mppe_in 9 "&8 / &5" "&1";;

(* Lean: side_gt (private) *)
let C1092MPPE_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  REWRITE_TAC[OO_SIDE]);;

(* Lean: wall_auxiliaries *)
let C1092MPPE_WALL_AUXILIARIES = prove
 (parse_term (Printf.sprintf "!%s. NPACK %s /\\ %s ==> %s /\\ %s /\\ %s /\\ %s" C1092AE_P C1092AE_P
    C1092MPPE_CTX (c1092mppe_in 8 "&1" "&113 / &50") (c1092mppe_in 9 "&87 / &50" "&1")
    (c1092mppe_in 10 "&3" "&87 / &50") (c1092mppe_in 11 "&113 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(SPECL (C1092MPPE_V @ [`c1092mppe_mppm`; mk_small_numeral k])
    C1092WC_WALL_AUXILIARY_POINT)) [0; 1; 2; 3] THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mppe_mppm; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let c1092mppe_wall_point k y x0 y0 =
  prove
   (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MPPE_CTX (c1092mppe_in (k + 8) x0 y0)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL (C1092MPPE_V @ [`c1092mppe_mppm`; mk_small_numeral k; y]) C1092WC_LOCAL_WALL_SEGMENT) THEN
    ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mppe_mppm; ARITH] THEN
    REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let c1092mppe_marker i code k x y =
  let bits = prove
   (parse_term (Printf.sprintf "%d IN bitset (EL %d c1092wc_code)" k i),
    REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
    REWRITE_TAC[bitset_bits code; IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV) in
  prove
   (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092AE_HYP (c1092mppe_in i x y)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i]) C1092WC_OWNERS_MARKERS) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(MP_TAC o SPEC (mk_small_numeral k)) THEN
    REWRITE_TAC[ARITH; bits; MARKER_EXPLICIT; VECTOR_2] THEN SIMP_TAC[]);;

(* local facts: marker 13 of owners 9, wall cover of owners 9, low wall point *)
let C1092MPPE_MARKER9 = c1092mppe_marker 9 8192 13 "&2" "&457 / &500";;
let C1092MPPE_BOTTOM_COVER = c1092ac_concrete C1092AC_WALL_COVER_TRANSPORTED `(true,false,false)` 9
  [`&8 / &5`, `&1`; `&12 / &5`, `&1`; `&2`, `&87 / &50`];;
let C1092MPPE_BOTTOM_LOW = c1092mppe_wall_point 1 `&161 / &100` "&161 / &100" "&1";;

let c1092mppe_q = c1092mmpe_q;;
let c1092mppe_sw q =
  match q with [c; s; u; v; a] ->
    [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c1092mppe_sw";;

let c1092mppe_disj i js =
  MAP_EVERY (fun j -> MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i; mk_small_numeral j])
    C1092WC_OWNERS_DISJOINT)) js THEN
  ASM_REWRITE_TAC[ARITH; ldisj] THEN REPEAT DISCH_TAC;;

(* Lean: omitted_bottom_bar *)
let C1092MPPE_OMITTED_BOTTOM_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> !x. &161 / &100 <= x ==> x <= &12 / &5 ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT (c1092mppe_in 9 "x" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th))
    [C1092MPPE_WALL_AUXILIARIES; C1092MPPE_MARKER9; C1092MPPE_BOTTOM_COVER;
     C1092AE_SOUTHWEST_MARKER; C1092MPPE_BOTTOM_LOW] THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPPE_SIDE_GT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  c1092mppe_disj 9 [4] THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 9 "&12 / &5" "&1")) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_disj(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL (c1092mppe_sw (c1092mppe_q 9)) C1092MPPE_SIDE_SIX_POINT) THEN
    REWRITE_TAC[LINSIDE_PULLSW] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&161 / &100`; `&12 / &5`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: omitted_bottom_inward *)
let C1092MPPE_OMITTED_BOTTOM_INWARD = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s /\\ %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT
    (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 5 "&113 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MPPE_OMITTED_BOTTOM_BAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&12 / &5` th) THEN MP_TAC(SPEC `&113 / &50` th)) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_LE_CONV) THEN REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th))
    [C1092MPPE_WALL_AUXILIARIES; C1092MMEN_SOUTHEAST_F_COVER; C1092AC_SOUTHEAST_G_COVER] THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`EL 5 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPPE_SIDE_GT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  c1092mppe_disj 5 [9; 10] THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 5 "&2" "&87 / &50")) ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 5 "&113 / &50" "&2")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 5 "&3" "&8 / &5")) ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C1092MS_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC (c1092mppe_q 5) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

(* Lean: omitted_bottom_neighbors *)
let C1092MPPE_TOP_TIP = c1092mppe_wall_point 3 `&161 / &100` "&239 / &100" "&3";;
let C1092MPPE_MARKER6 = c1092mppe_marker 6 1024 10 "&47 / &20" "&47 / &20";;

let C1092MPPE_OMITTED_BOTTOM_NEIGHBORS = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> (%s /\\ %s) /\\ (%s /\\ %s)"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT
    (c1092mppe_in 6 "&3" "&113 / &50") (c1092mppe_in 6 "&3" "&12 / &5")
    (c1092mppe_in 10 "&3" "&87 / &50") (c1092mppe_in 10 "&3" "&8 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th))
    [C1092MPPE_OMITTED_BOTTOM_INWARD; C1092MPPE_WALL_AUXILIARIES; C1092MPPE_TOP_TIP;
     C1092MMPE_CORNER2; C1092MPPE_MARKER6] THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`EL 6 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPPE_SIDE_GT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  c1092mppe_disj 6 [5; 11; 2] THEN c1092mppe_disj 10 [5; 6] THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 6 "&3" "&12 / &5")) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C1092AC_NORTHEAST_G_COVER) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 10 "&3" "&8 / &5")) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C1092AC_RIGHT_G_COVER) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 6 "&3" "&113 / &50")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_neg(parse_term (c1092mppe_in 6 "&12 / &5" "&3"))) ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C1092CTG_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC (c1092mppe_q 6 @ [`&39 / &100`; `&13 / &50`]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL C1092AC_NORTHEAST_F_COVER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092MS_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC (c1092mmen_pully (c1092mppe_q 6)) THEN
  REWRITE_TAC[LINSIDE_PULLY; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN ASM_MESON_TAC[]);;
