(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/InwardTips.lean                     *)
(* (N12Compact.C1092MMMPInwardTips).  The actual northwest excludes the     *)
(* outer left auxiliary; the strict second inward tip follows.               *)
(* Conventions of CP_C1092_MMMP_PointCore.ml / CP_C1092_MMMP_Origins.ml      *)
(* (charts via c1092mo_layers: LINSIDE_PULLX, CCIP_INSIDE_TRANSLATED,        *)
(* LINSIDE_PULLSW).  C1092MMMPOuterArm.impossible C1092OARM_IMPOSSIBLE,      *)
(* CommonCases.InwardPoint.strong_original CCIP_STRONG_ORIGINAL.             *)
(* Tag C1092MIT_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_PointCore.ml";;
needs "n12/geometry/CP_C1092_MMMP_OuterArm.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;

(* Lean: missing_outer *)
let C1092MIT_MISSING_OUTER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ~%s"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX (c1092mmpe_in 7 "&1" "&12 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN DISCH_TAC THEN
  let tC, eqC = c1092mo_layers 7 [C1092MO_X; c1092mo_tr `&2` `&2`]
  and tW, eqW = c1092mo_layers 8 [C1092MO_X; c1092mo_tr `&2` `&2`] in
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let top = c1092mo_use C1092MMPE_TOP_PAIR in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let cut = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MPC_CUT)) in
  let box8 = REWRITE_RULE[lcont] (c1092mo_box 8) in
  let facts = [c1092mo_punit 7 tC; c1092mo_punit 8 tW; c1092mo_pos (); c1092mo_side ();
               c1092mo_use C1092MPC_NORTHWEST_CENTER;
               c1092mo_seed 7 (`&33 / &20`, `&47 / &20`); CONJUNCT1 nw; CONJUNCT2 nw;
               c1092mo_excl 7 11 (CONJUNCT1 top);
               c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
               c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
               c1092mo_seed 8 (`&457 / &500`, `&2`); CONJUNCT1 wa; c1092mo_apart 7 8] in
  MATCH_MP_TAC (SPECL (tC @ tW) C1092OARM_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj] THEN CONV_TAC (c1092mo_conv (eqC @ eqW)) THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
         REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box8) THEN REAL_ARITH_TAC;
         MP_TAC cut THEN MP_TAC (c1092mo_unit 8) THEN REWRITE_TAC[lcy] THEN REAL_ARITH_TAC]);;

(* Lean: second_tip *)
let C1092MIT_SECOND_TIP = prove
 (c1092mmpe_stmt 7 "&199 / &100" "&127 / &50",
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  let t, eqs = c1092mo_layers 7 [C1092MO_SW] in
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let facts = [c1092mo_punit 7 t; c1092mo_side ();
               c1092mo_seed 7 (`&33 / &20`, `&47 / &20`); CONJUNCT1 nw; CONJUNCT2 nw;
               c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
               c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
               c1092mo_use C1092MIT_MISSING_OUTER] in
  MP_TAC(SPECL t CCIP_STRONG_ORIGINAL) THEN CONV_TAC (c1092mo_conv eqs) THEN
  ANTS_TAC THENL
   [MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[]]);;
