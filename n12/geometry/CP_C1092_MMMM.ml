(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMM.lean (N12Compact.C1092MMMM).        *)
(* The full original MMMM entrance and the genuine BranchEnding 2 contract.  *)
(* Conventions of CP_C1092_MMMMWalls.ml / CP_C1092_MMMMEntrance.ml: owners   *)
(* p i is the OriginalOwners 5-tuple at mask EL i c1092wc_code (side l),     *)
(* WallContext p mmmm is c1092wc_ctx .. c1092mmen_mmmm, BranchEnding k is    *)
(* c1092wsy_ending k.  translate Q 2 2 (RigidCharts) is the tuple            *)
(* (c, s, u - c * &2 - s * &2, v + (s * &2 - c * &2), a)                     *)
(* (C1092RC_INSIDE_TRANSLATE).  MMMMEnding.impossible: C1092MME_IMPOSSIBLE;  *)
(* MMMMStrictCore.northeast_triangle: C1092MMSC_NORTHEAST_TRIANGLE;          *)
(* southeast_pair / northwest_pair: C1092MMEN_*; the Walls origins:          *)
(* C1092MMW_RIGHT_ORIGIN / C1092MMW_TOP_ORIGIN.  Tag C1092MM_.               *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMMWalls.ml";;
needs "n12/geometry/CP_C1092_MMMMEnding.ml";;

(* Lean: side_gt / side_same (private): OO_SIDE and the common side l *)

let c1092mm_tr q =
  match q with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y in
      [c; s; sub (sub u (mul c `&2`)) (mul s `&2`); add v (sub (mul s `&2`) (mul c `&2`)); a]
  | _ -> failwith "c1092mm_tr";;

let C1092MM_MARKER7 = c1092mmsc_marker true 7 2048 11 "&33 / &20" "&47 / &20";;

(* local_wall_segment at wall 0 (owner 8), as C1092MMEN_BOTTOM_TIP for wall 1 *)
let C1092MM_LEFT_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMEN_CTX (c1092mmen_in 8 "&1" "&239 / &100")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMEN_V @ [`c1092mmen_mmmm`; `0`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmen_mmmm; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* Lean: impossible *)
let C1092MM_IMPOSSIBLE = prove
 (c1092mmsc_stmt "F",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let hyp = CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`) in
  let fix th = PROVE_HYP hyp (PROVE_HYP (ASSUME (parse_term C1092MMEN_CTX)) th) in
  let triangle = fix (c1092mmw_ctx C1092MMSC_NORTHEAST_TRIANGLE) in
  let t0 = CONJUNCT1 triangle and t1 = CONJUNCT1 (CONJUNCT2 triangle)
  and t2 = CONJUNCT2 (CONJUNCT2 triangle) in
  let seg th0 th1 =
    let th = MATCH_MP C1092WC_INSIDE_SEGMENT (CONJ th0 (CONJ th1 (CONJ
      (REAL_ARITH `&0 <= &39 / &50`) (REAL_ARITH `&39 / &50 <= &1`)))) in
    CONV_RULE REAL_RAT_REDUCE_CONV th in
  let innerX = seg t0 t1 and innerY = seg t0 t2 in
  let east = fix (c1092mmw_ctx C1092MMEN_SOUTHEAST_PAIR) in
  let west = fix (c1092mmw_ctx C1092MMEN_NORTHWEST_PAIR) in
  let bottom = fix (UNDISCH (SPEC_ALL C1092MMEN_BOTTOM_TIP)) in
  let left = fix (UNDISCH (SPEC_ALL C1092MM_LEFT_TIP)) in
  let cornerE = fix (c1092mmw_corner 1) and cornerW = fix (c1092mmw_corner 3) in
  let right = fix (c1092mmw_ctx C1092MMW_RIGHT_ORIGIN) in
  let top = fix (c1092mmw_ctx C1092MMW_TOP_ORIGIN) in
  let dis i j = fix (c1092mmw_dis i j) in
  let ex th i j = let x, y = (match snd (strip_comb (concl th)) with
        [_; _; _; _; _; x; y] -> x, y | _ -> failwith "ex") in c1092mmw_excl th (dis i j) x y in
  let facts =
    [fix (c1092mmw_unit 6); fix (c1092mmw_unit 5); fix (c1092mmw_unit 7);
     fix C1092MMW_SIDE; fix C1092MMW_POS;
     t0; t1; t2; fix (c1092mmw_inst C1092MMSC_MARKER6); fix (c1092mmw_inst C1092MMW_MARKER5);
     fix (c1092mmw_inst C1092MM_MARKER7);
     CONJUNCT1 east; CONJUNCT2 east; CONJUNCT1 west; CONJUNCT2 west;
     ex cornerE 5 1; ex right 5 10; ex bottom 5 9; ex innerX 5 6;
     ex cornerW 7 3; ex top 7 11; ex left 7 8; ex innerY 7 6;
     dis 6 5; dis 6 7] in
  MATCH_MP_TAC (SPECL (c1092mm_tr (c1092mmsc_q 6) @ c1092mm_tr (c1092mmsc_q 5) @
                       c1092mm_tr (c1092mmsc_q 7)) C1092MME_IMPOSSIBLE) THEN
  REWRITE_TAC[c1092mme_data; ldisj; C1092RC_INSIDE_TRANSLATE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

(* Lean: action (local fact of adjacentPair) *)
let C1092MM_ACTION = prove
 (`forall k. k < 4 ==> c1092ws_branch_action (false,false,true) (c1092ws_canonical_branch 2) k = c1092mmen_mmmm k`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN CONV_TAC c1092ae_act_conv THEN
  REWRITE_TAC[c1092ws_canonical_branch; c1092mmen_mmmm] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Lean: adjacentPair *)
let C1092MM_ADJACENT_PAIR = prove
 (`c1092wsy_ending 2`,
  let g = `(false,false,true)` and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  REWRITE_TAC[c1092wsy_ending] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists d1 d2 e1 e2. c1092ot_pk (false,false,true) (c1,c2,a,b) = (d1,d2,e1,e2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092wc_ctx d1 d2 e1 e2 l c1092mmen_mmmm` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
    EXISTS_TAC `c1092ws_branch_action (false,false,true) (c1092ws_canonical_branch 2)` THEN
    REWRITE_TAC[C1092MM_ACTION] THEN
    MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]
    C1092MM_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;
