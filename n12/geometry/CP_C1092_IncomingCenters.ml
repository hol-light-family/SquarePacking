(* ========================================================================= *)
(* Phase 2: Compact/Completion/C1092/IncomingCenters.lean                    *)
(* (N12Compact.C1092IncomingCenters).  Every incoming physical wall pair     *)
(* forces its genuine central owner to contain (2,2).  southeast / northwest *)
(* apply OppositePair.southwest_center (C1092OP_SOUTHWEST_CENTER) to the     *)
(* reflected packing g.pullPacking p (c1092ot_pk), as in Lean.               *)
(* Conventions of CP_C1092_OppositePair.ml.  Tag C1092IC_.                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_OppositePair.ml";;

(* apply base (a centre theorem for owner idx) to g.pullPacking p *)
let c1092ic_transport_tac base g idx =
  let pk = `c1092ot_pk`
  and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
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
                mk_comb(mk_comb(`c1092ws_branch_action`, g), `br:num->bool`)] base) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC c1092ae_act_conv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([g] @ v4 @ [`l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`;
                 mk_small_numeral idx]) C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral idx))] THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];;


(* Lean: southeast *)
let C1092IC_SOUTHEAST = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ br 2 /\\ ~br 1 ==> %s"
   C1092AE_P C1092AE_HYP (c1092ae_in C1092AE_P 5 "&2" "&2")),
  c1092ic_transport_tac C1092OP_SOUTHWEST_CENTER `(false,true,false)` 4);;

(* Lean: northwest *)
let C1092IC_NORTHWEST = prove
 (parse_term (Printf.sprintf
   "!%s br. %s /\\ c1092wc_ctx c1 c2 a b l br /\\ ~br 0 /\\ br 3 ==> %s"
   C1092AE_P C1092AE_HYP (c1092ae_in C1092AE_P 7 "&2" "&2")),
  c1092ic_transport_tac C1092OP_SOUTHWEST_CENTER `(false,false,true)` 4);;

let c1092ic_canonical_tac th k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN
  EXISTS_TAC (mk_comb(`c1092ws_canonical_branch`, mk_small_numeral k)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092ws_canonical_branch] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];;

(* Lean: exceptional *)
let C1092IC_EXCEPTIONAL = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c1092wc_ctx c1 c2 a b l (c1092ws_canonical_branch 1) ==> %s"
   C1092AE_P C1092AE_HYP (c1092ae_in C1092AE_P 4 "&2" "&2")),
  c1092ic_canonical_tac C1092OP_SOUTHWEST_CENTER 1);;

(* Lean: adjacent *)
let C1092IC_ADJACENT = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c1092wc_ctx c1 c2 a b l (c1092ws_canonical_branch 2) ==> %s"
   C1092AE_P C1092AE_HYP (c1092ae_in C1092AE_P 5 "&2" "&2")),
  c1092ic_canonical_tac C1092IC_SOUTHEAST 2);;
