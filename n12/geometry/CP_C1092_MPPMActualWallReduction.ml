(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualWallReduction.lean             *)
(* (N12Compact.C1092MPPMActualWallReduction).  Complete original-wall        *)
(* entrance to the remaining MPPM central problem: a simultaneous quarter    *)
(* turn transports every actual square, so each literal ordinary wall        *)
(* auxiliary is strict.  (Lean header: "Source only, uncompiled".)           *)
(* Conventions of CP_C1092_MPPMOmissions.ml: g.pullPacking p is              *)
(* (d1,d2,e1,e2) with c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2);              *)
(* family_transport C1092OT_FAMILY_TRANSPORT, owners_transport               *)
(* C1092OT_OWNERS_TRANSPORT, context_transport C1092CT_CONTEXT_TRANSPORT     *)
(* (branchAction g mppm = mppm checked on the four walls), inside of a       *)
(* pulled owner C1092CT_INSIDE_PULL.  Missing p k is c1092mom_missing        *)
(* (k : Fin 4 as k < 4); ordinary_walls C1092MOM_ORDINARY_WALLS;             *)
(* Ordinary / Inward / Elbow and no_omission_cover c1092mcc_* /              *)
(* C1092MCC_NO_OMISSION_COVER; MPPMActualTwoFifths.impossible                *)
(* C1092MPATF_IMPOSSIBLE.  Tag C1092MPAWR_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualTwoFifths.ml";;
needs "n12/geometry/CP_C1092_MPPMCentralCover.ml";;

(* Lean: bottom_ordinary *)
let C1092MPAWR_BOTTOM_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX
    (c1092mppe_in 9 "&8 / &5" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPATF_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* apply bottom_ordinary to g.pullPacking p *)
let c1092mpawr_transport g =
  let v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  let d5 = [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_exists(`d1:num->real`, list_mk_exists([`d2:num->real`; `e1:num->real`; `e2:num->real`],
     mk_eq(list_mk_comb(`c1092ot_pk`, [g; `(c1:num->real,c2:num->real,a:num->real,b:num->real)`]),
           `(d1:num->real,d2:num->real,e1:num->real,e2:num->real)`))))
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092wc_ctx d1 d2 e1 e2 l c1092mppe_mppm` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
    EXISTS_TAC (mk_comb(mk_comb(`c1092ws_branch_action`, g), `c1092mppe_mppm`)) THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN CONV_TAC c1092ae_act_conv THEN
      REWRITE_TAC[c1092mppe_mppm] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL d5 C1092MPAWR_BOTTOM_ORDINARY) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL ([g] @ v4 @ [`l:real`] @ fst (chop_list 4 d5) @ [`9`]) C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), `9`))] THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];;

let c1092mpawr_stmt i x y =
  parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX
    (c1092mppe_in i x y));;

(* Lean: right_ordinary *)
let C1092MPAWR_RIGHT_ORDINARY = prove
 (c1092mpawr_stmt 10 "&3" "&8 / &5", c1092mpawr_transport `(true,true,false)`);;

(* Lean: top_ordinary *)
let C1092MPAWR_TOP_ORDINARY = prove
 (c1092mpawr_stmt 11 "&12 / &5" "&3", c1092mpawr_transport `(false,true,true)`);;

(* Lean: left_ordinary *)
let C1092MPAWR_LEFT_ORDINARY = prove
 (c1092mpawr_stmt 8 "&1" "&12 / &5", c1092mpawr_transport `(true,false,true)`);;

(* Lean: no_missing *)
let C1092MPAWR_NO_MISSING = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> !k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL C1092MPPE_V th) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC)
    [C1092MPAWR_LEFT_ORDINARY; C1092MPAWR_BOTTOM_ORDINARY;
     C1092MPAWR_RIGHT_ORDINARY; C1092MPAWR_TOP_ORDINARY] THEN
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN
  REWRITE_TAC[c1092mom_missing] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092MOM_OPOINT_ELS @ [FST; SND]) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: wall_pairs *)
let C1092MPAWR_WALL_PAIRS = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> (%s /\\ %s) /\\ (%s /\\ %s) /\\ (%s /\\ %s) /\\ (%s /\\ %s)"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX
    (c1092mppe_in 8 "&1" "&113 / &50") (c1092mppe_in 8 "&1" "&12 / &5")
    (c1092mppe_in 9 "&8 / &5" "&1") (c1092mppe_in 9 "&87 / &50" "&1")
    (c1092mppe_in 10 "&3" "&87 / &50") (c1092mppe_in 10 "&3" "&8 / &5")
    (c1092mppe_in 11 "&12 / &5" "&3") (c1092mppe_in 11 "&113 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (SPECL C1092MPPE_V C1092MOM_ORDINARY_WALLS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAWR_NO_MISSING) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: southwest_cover *)
let C1092MPAWR_SOUTHWEST_COVER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (SPECL C1092MPPE_V C1092MCC_NO_OMISSION_COVER) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAWR_NO_MISSING) THEN
  ASM_REWRITE_TAC[]);;
