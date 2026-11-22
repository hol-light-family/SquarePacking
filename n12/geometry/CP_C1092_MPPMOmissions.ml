(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOmissions.lean                       *)
(* (namespace N12Compact.C1092MPPMOmissions).  The complete actual-wall      *)
(* omission split: whole-packing transforms keep the MPPM context and move   *)
(* the original owner of every point; two omitted ordinary wall auxiliaries  *)
(* are impossible.  Conventions of CP_C1092_MPPMEntrance.ml /                *)
(* CP_C1092_MMMMWalls.ml: g.pullPacking p is (d1,d2,e1,e2) with              *)
(* c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2); family_transport =              *)
(* C1092OT_FAMILY_TRANSPORT, owners_transport = C1092OT_OWNERS_TRANSPORT,    *)
(* context_transport = C1092CT_CONTEXT_TRANSPORT (branchAction g mppm = mppm *)
(* checked on the four walls), inside of a pulled owner C1092CT_INSIDE_PULL. *)
(* wallOwner k / centralOwner k = EL k c1092wc_wall / EL k c1092wc_central   *)
(* (k < 4).  bottom_center = C1092MOC_BOTTOM_CENTER.  Tag C1092MOM_.         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOmissionCenter.ml";;

(* Lean: ordinaryPoint *)
let c1092mom_opoint = new_definition
 `c1092mom_opoint = [(&1, &12 / &5); (&8 / &5, &1); (&3, &8 / &5); (&12 / &5, &3)]`;;

(* Lean: Missing *)
let c1092mom_missing = new_definition
 `c1092mom_missing (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (k:num) <=>
    ~linside (ooc c1 c2 a b l (EL (EL k c1092wc_wall) c1092wc_code))
             (oos c1 c2 a b l (EL (EL k c1092wc_wall) c1092wc_code))
             (oou c1 c2 a b l (EL (EL k c1092wc_wall) c1092wc_code))
             (oov c1 c2 a b l (EL (EL k c1092wc_wall) c1092wc_code)) l
             (FST (EL k c1092mom_opoint)) (SND (EL k c1092mom_opoint))`;;

let C1092MOM_OPOINT_ELS = el_lookups c1092mom_opoint;;

(* apply bottom_center to g.pullPacking p *)
let c1092mom_transport g =
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
  MP_TAC(SPECL d5 C1092MOC_BOTTOM_CENTER) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL ([g] @ v4 @ [`l:real`] @ fst (chop_list 4 d5) @ [mk_small_numeral i]) C1092OT_OWNERS_TRANSPORT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th])) [9; 5] THEN
  REWRITE_TAC(map (fun i -> c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i))) [9; 5]) THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let c1092mom_stmt omit i =
  parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ ~%s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX omit
    (c1092mppe_in i "&2" "&2"));;

(* Lean: right_center *)
let C1092MOM_RIGHT_CENTER = prove
 (c1092mom_stmt (c1092mppe_in 10 "&3" "&8 / &5") 6, c1092mom_transport `(true,true,false)`);;

(* Lean: top_center *)
let C1092MOM_TOP_CENTER = prove
 (c1092mom_stmt (c1092mppe_in 11 "&12 / &5" "&3") 7, c1092mom_transport `(false,true,true)`);;

(* Lean: left_center *)
let C1092MOM_LEFT_CENTER = prove
 (c1092mom_stmt (c1092mppe_in 8 "&1" "&12 / &5") 4, c1092mom_transport `(true,false,true)`);;

let C1092MOM_CENTRAL_OWNER =
  "(ooc c1 c2 a b l (EL (EL k c1092wc_central) c1092wc_code)) (oos c1 c2 a b l (EL (EL k c1092wc_central) c1092wc_code)) (oou c1 c2 a b l (EL (EL k c1092wc_central) c1092wc_code)) (oov c1 c2 a b l (EL (EL k c1092wc_central) c1092wc_code)) l";;

(* Lean: center *)
let C1092MOM_CENTER = prove
 (parse_term (Printf.sprintf "!%s k. %s /\\ %s /\\ k < 4 /\\ c1092mom_missing c1 c2 a b l k ==> linside %s (&2) (&2)"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MOM_CENTRAL_OWNER),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mom_missing] THEN STRIP_TAC THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN
  RULE_ASSUM_TAC(REWRITE_RULE(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092MOM_OPOINT_ELS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  REWRITE_TAC(Array.to_list C1092WC_CENTRAL_ELS) THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [C1092MOM_LEFT_CENTER; C1092MOC_BOTTOM_CENTER; C1092MOM_RIGHT_CENTER; C1092MOM_TOP_CENTER]));;

let C1092MOM_CENTRAL_DISTINCT = prove
 (`forall i j. i < 4 /\ j < 4 /\ ~(i = j)
     ==> EL i c1092wc_central < 12 /\ EL j c1092wc_central < 12 /\
         ~(EL i c1092wc_central = EL j c1092wc_central)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092WP_ENUM_TAC `i:num` 4 THEN C1092WP_ENUM_TAC `j:num` 4 THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  REWRITE_TAC(Array.to_list C1092WC_CENTRAL_ELS) THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM CONTR_TAC);;

(* Lean: at_most_one *)
let C1092MOM_AT_MOST_ONE = prove
 (parse_term (Printf.sprintf "!%s i j. %s /\\ %s /\\ i < 4 /\\ j < 4 /\\ c1092mom_missing c1 c2 a b l i /\\ c1092mom_missing c1 c2 a b l j ==> i = j"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX),
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`i:num`; `j:num`] C1092MOM_CENTRAL_DISTINCT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`EL i c1092wc_central`; `EL j c1092wc_central`]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&2`]) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL (C1092MPPE_V @ [`i:num`]) C1092MOM_CENTER);
    MP_TAC(SPECL (C1092MPPE_V @ [`j:num`]) C1092MOM_CENTER)] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: exhaustive *)
let C1092MOM_EXHAUSTIVE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> (!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k) \\/ (?k. k < 4 /\\ c1092mom_missing c1 c2 a b l k /\\ !j. j < 4 /\\ c1092mom_missing c1 c2 a b l j ==> j = k)"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX),
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `forall k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SPECL C1092MPPE_V C1092MOM_AT_MOST_ONE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: ordinary_walls *)
let C1092MOM_ORDINARY_WALLS = prove
 (parse_term (Printf.sprintf "!%s. NPACK %s /\\ %s /\\ (!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k) ==> (%s /\\ %s) /\\ (%s /\\ %s) /\\ (%s /\\ %s) /\\ (%s /\\ %s)"
    C1092AE_P C1092AE_P C1092MPPE_CTX
    (c1092mppe_in 8 "&1" "&113 / &50") (c1092mppe_in 8 "&1" "&12 / &5")
    (c1092mppe_in 9 "&8 / &5" "&1") (c1092mppe_in 9 "&87 / &50" "&1")
    (c1092mppe_in 10 "&3" "&87 / &50") (c1092mppe_in 10 "&3" "&8 / &5")
    (c1092mppe_in 11 "&12 / &5" "&3") (c1092mppe_in 11 "&113 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MPPE_WALL_AUXILIARIES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun k -> FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o check (is_forall o concl)))
    [0; 1; 2; 3] THEN
  REWRITE_TAC[c1092mom_missing; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092MOM_OPOINT_ELS @ [FST; SND]) THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;
