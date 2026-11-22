(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPM.lean (N12Compact.C1092MPPM; Lean    *)
(* header: "Source only, without compiler or replay acceptance").  The       *)
(* original windmill branch.  WallContext p mppm C1092MPPE_CTX; BranchEnding *)
(* c1092wsy_ending; canonicalBranch / branchAction c1092ws_canonical_branch / *)
(* c1092ws_branch_action; context_transport / family_transport               *)
(* C1092CT_CONTEXT_TRANSPORT / C1092OT_FAMILY_TRANSPORT (+ C1092OT_NPACK);   *)
(* MPPMActualInward.ordinary C1092MAIR_ORDINARY; MPPMOrdinaryCycle.impossible*)
(* C1092MOEN_IMPOSSIBLE.  Tag C1092MPPMW_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardReduction.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryEnding.ml";;

(* Lean: impossible *)
let C1092MPPMW_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "forall %s. %s /\\ %s ==> false" C1092AE_P C1092AE_HYP C1092MPPE_CTX),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL C1092MOCD_V C1092MOEN_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL C1092MOCD_V C1092MAIR_ORDINARY) THEN ASM_REWRITE_TAC[]);;

(* Lean: windmill *)
let C1092MPPMW_WINDMILL = prove
 (`c1092wsy_ending 0`,
  REWRITE_TAC[c1092wsy_ending] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mapc_choose_tac `(false,false,true)` C1092MOCD_V4 C1092MOCD_D THEN
  MATCH_MP_TAC (SPECL (C1092MOCD_D @ [`l:real`]) C1092MPPMW_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (`(false,false,true)` :: C1092MOCD_V4) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (`(false,false,true)` :: C1092MOCD_V4) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
    EXISTS_TAC `c1092ws_branch_action (false,false,true) (c1092ws_canonical_branch 0)` THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN
      CONV_TAC c1092ae_act_conv THEN
      REWRITE_TAC[c1092ws_canonical_branch; c1092mppe_mppm] THEN
      CONV_TAC(REDEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC C1092MOCD_V4 THEN
      ASM_REWRITE_TAC[]]]);;
