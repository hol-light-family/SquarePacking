(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/PointCore.lean                      *)
(* (N12Compact.C1092MMMPPointCore).  The actual NW center, left halfpoint    *)
(* and complete diagonal interval needed by the shorter MMMP ending.         *)
(* Conventions of CP_C1092_MMMP_Origins.ml / CP_C1092_MMMPEntrance.ml:       *)
(* owners p i is the OriginalOwners 5-tuple at mask EL i c1092wc_code (side  *)
(* l), WallContext p mmmp is c1092wc_ctx .. c1092mmpe_mmmp; the charts       *)
(* (pullX Q).translated 2 2 are built with c1092mo_layers (LINSIDE_PULLX,    *)
(* CCIP_INSIDE_TRANSLATED).  C1092IncomingCenters.northwest C1092IC_NORTHWEST,*)
(* C1092InwardCenterDiagonal.diagonal C1092ICD_DIAGONAL,                     *)
(* C1092MMMPCenterCrosspoint.point C1092MCC_POINT, inside_segment            *)
(* C1092WC_INSIDE_SEGMENT, marker_point = seeds (oo_seed).  Tag C1092MPC_.   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_Origins.ml";;
needs "n12/geometry/CP_C1092_IncomingCenters.ml";;
needs "n12/geometry/CP_C1092_InwardCenterDiagonal.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCrosspoint.ml";;

(* Lean: northwest_center *)
let C1092MPC_NORTHWEST_CENTER = prove
 (c1092mmpe_stmt 7 "&2" "&2",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`]) C1092IC_NORTHWEST) THEN
  ASM_REWRITE_TAC[c1092mmpe_mmmp; ARITH]);;

(* closes the conjuncts of a converted antecedent from facts *)
let C1092MPC_CLOSE_TAC facts =
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC];;

(* Lean: northwest_diagonal_interval *)
let C1092MPC_NORTHWEST_DIAGONAL_INTERVAL = prove
 (parse_term (Printf.sprintf "!%s k. %s /\\ %s /\\ &7 / &20 <= k /\\ k pow 2 <= &151 / &400 ==> %s"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX (c1092mmpe_in 7 "&2 - k" "&2 + k")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  let t, eqs = c1092mo_layers 7 [C1092MO_X; c1092mo_tr `&2` `&2`] in
  let facts = [c1092mo_punit 7 t; c1092mo_pos (); c1092mo_side ();
               c1092mo_use C1092MPC_NORTHWEST_CENTER;
               c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
               c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
               c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`))] in
  MP_TAC(SPECL (t @ [`k:real`]) C1092ICD_DIAGONAL) THEN
  CONV_TAC (c1092mo_conv eqs) THEN
  ANTS_TAC THENL [C1092MPC_CLOSE_TAC facts; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&2 + k) = &2 - k`]);;

(* Lean: northwest_diagonal *)
let C1092MPC_NORTHWEST_DIAGONAL = prove
 (c1092mmpe_stmt 7 "&3 / &2" "&5 / &2",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`&1 / &2`]) C1092MPC_NORTHWEST_DIAGONAL_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Lean: northwest_long_diagonal *)
let C1092MPC_NORTHWEST_LONG_DIAGONAL = prove
 (c1092mmpe_stmt 7 "&139 / &100" "&261 / &100",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`&61 / &100`]) C1092MPC_NORTHWEST_DIAGONAL_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

(* segment (local fact of northwest_north): inside_segment between (1,2) and (1,239/100) *)
let C1092MPC_SEGMENT = prove
 (`forall c s u v a. linside c s u v a (&1) (&2) /\ linside c s u v a (&1) (&239 / &100)
     ==> forall y. &0 <= y ==> y <= &39 / &100 ==> linside c s u v a (&1) (&2 + y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&2`; `&1`; `&239 / &100`;
                `&100 / &39 * y`] C1092WC_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* the left wall tip: local_wall_segment at wall 0 *)
let C1092MPC_LEFT_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMPE_CTX (c1092mmpe_in 8 "&1" "&239 / &100")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; `0`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* cut (local fact of northwest_north): the left wall frame is the owner 8 itself *)
let C1092MPC_CUT = prove
 (parse_term (Printf.sprintf "!%s. %s ==> &2 <= lcy %s" C1092AE_P C1092MMPE_CTX (c1092ae_own C1092AE_P 8)),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ARITH; c1092mmpe_mmmp; c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN SIMP_TAC[]);;

(* Lean: northwest_north *)
let C1092MPC_NORTHWEST_NORTH = prove
 (c1092mmpe_stmt 7 "&2" "&5 / &2",
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  let tC, eqC = c1092mo_layers 7 [C1092MO_X; c1092mo_tr `&2` `&2`]
  and tW, eqW = c1092mo_layers 8 [C1092MO_X; c1092mo_tr `&2` `&2`] in
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let left = c1092mo_use C1092MO_LEFT_ORIGIN in
  let tip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MPC_LEFT_TIP)) in
  let cut = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MPC_CUT)) in
  let box8 = REWRITE_RULE[lcont] (c1092mo_box 8) in
  let facts = [c1092mo_punit 7 tC; c1092mo_punit 8 tW; c1092mo_pos (); c1092mo_side ();
               c1092mo_use C1092MPC_NORTHWEST_CENTER;
               c1092mo_seed 7 (`&33 / &20`, `&47 / &20`); CONJUNCT1 nw; CONJUNCT2 nw;
               c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
               c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
               c1092mo_seed 8 (`&457 / &500`, `&2`); CONJUNCT1 wa;
               MATCH_MP C1092MPC_SEGMENT (CONJ left tip); c1092mo_apart 7 8] in
  MP_TAC(SPECL (tC @ tW) C1092MCC_POINT) THEN
  REWRITE_TAC[ldisj] THEN CONV_TAC (c1092mo_conv (eqC @ eqW)) THEN
  ANTS_TAC THENL
   [MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
           REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box8) THEN REAL_ARITH_TAC;
           MP_TAC cut THEN MP_TAC (c1092mo_unit 8) THEN REWRITE_TAC[lcy] THEN REAL_ARITH_TAC];
    SIMP_TAC[]]);;
