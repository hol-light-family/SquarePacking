(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardSymmetry.lean            *)
(* (N12Compact.C1092MPPMActualInward).  Whole-packing opposite-sector        *)
(* transport used by the inward case split.  Conventions of                  *)
(* CP_C1092_MPPMActualPositiveOrder.ml / CP_C1092_MPPMActualNonordinary.ml:  *)
(* owners p i at mask EL i c1092wc_code, side l; WallContext p mppm          *)
(* C1092MPPE_CTX; halfTurn.pullPacking p is (d1,d2,e1,e2) with               *)
(* c1092ot_pk c1092mais_halfTurn (c1,c2,a,b) = (d1,d2,e1,e2); Ordinary /     *)
(* Inward of an OpenSquare are c1092mcc_ordinary / c1092mcc_inward;          *)
(* NorthOrdinary p / NorthInward p are c1092mais_northOrdinary /             *)
(* c1092mais_northInward c1 c2 a b l.  Used: context_transport               *)
(* (C1092MPAPO_ROTATION_CONTEXT, halfTurn = rotation 2), owners_transport    *)
(* C1092OT_OWNERS_TRANSPORT / C1092CT_INSIDE_PULL, ordinary_or_inward        *)
(* C1092MANO_ORDINARY_OR_INWARD.  Tag C1092MAIS_.                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardPoints.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinary.ml";;

(* Lean: halfTurn *)
let c1092mais_halfTurn = new_definition `c1092mais_halfTurn = (false,true,true)`;;

(* Lean: NorthOrdinary *)
let c1092mais_northOrdinary = new_definition (parse_term (Printf.sprintf
  "c1092mais_northOrdinary (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=> %s /\\ %s"
  (c1092mppe_in 6 "&3" "&113 / &50") (c1092mppe_in 6 "&3" "&12 / &5")));;

(* Lean: NorthInward *)
let c1092mais_northInward = new_definition (parse_term (Printf.sprintf
  "c1092mais_northInward (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=> %s /\\ %s"
  (c1092mppe_in 6 "&2" "&113 / &50") (c1092mppe_in 6 "&113 / &50" "&2")));;

let C1092MAIS_PK = "c1092ot_pk c1092mais_halfTurn (c1,c2,a,b) = (d1,d2,e1,e2)";;
let C1092MAIS_D5 = c1092mpapo_d4 "" @ [`l:real`];;
let C1092MAIS_DOWN4 = c1092ae_own "d1 d2 e1 e2 l" 4;;
let C1092MAIS_OWN4 = c1092ae_own C1092AE_P 4;;
let C1092MAIS_START_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[c1092mais_halfTurn]);;

(* Lean: half_context *)
let C1092MAIS_HALF_CONTEXT = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s /\\ %s ==> c1092wc_ctx d1 d2 e1 e2 l c1092mppe_mppm"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MAIS_PK),
  C1092MAIS_START_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "" @ [`2`]) C1092MPAPO_ROTATION_CONTEXT) THEN
  ASM_REWRITE_TAC(ARITH :: C1092MPAPO_ROT_ELS));;

(* Lean: half_inside *)
let C1092MAIS_HALF_INSIDE = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 i x y. %s /\\ %s /\\ i < 12 ==>
      (linside (ooc d1 d2 e1 e2 l (EL i c1092wc_code)) (oos d1 d2 e1 e2 l (EL i c1092wc_code))
               (oou d1 d2 e1 e2 l (EL i c1092wc_code)) (oov d1 d2 e1 e2 l (EL i c1092wc_code)) l x y <=>
       linside (ooc c1 c2 a b l (EL (c1092ws_owner_action c1092mais_halfTurn i) c1092wc_code))
               (oos c1 c2 a b l (EL (c1092ws_owner_action c1092mais_halfTurn i) c1092wc_code))
               (oou c1 c2 a b l (EL (c1092ws_owner_action c1092mais_halfTurn i) c1092wc_code))
               (oov c1 c2 a b l (EL (c1092ws_owner_action c1092mais_halfTurn i) c1092wc_code)) l
               (&4 - x) (&4 - y))"
    C1092AE_P C1092AE_HYP C1092MAIS_PK),
  C1092MAIS_START_TAC THEN REWRITE_TAC[c1092mais_halfTurn] THEN
  MP_TAC(SPECL ([`(false,true,true)`] @ C1092MPAPO_V4 @ [`l:real`] @ c1092mpapo_d4 "" @ [`i:num`])
    C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF]);;

let c1092mais_iff_tac idx =
  C1092MAIS_START_TAC THEN
  REWRITE_TAC[c1092mcc_ordinary; c1092mcc_inward; c1092mais_northOrdinary; c1092mais_northInward] THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(false,true,true)` idx;;

(* Lean: half_ordinary *)
let C1092MAIS_HALF_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s ==> (c1092mcc_ordinary %s <=> c1092mais_northOrdinary %s)"
    C1092AE_P C1092AE_HYP C1092MAIS_PK C1092MAIS_DOWN4 C1092AE_P),
  c1092mais_iff_tac [4]);;

(* Lean: half_inward *)
let C1092MAIS_HALF_INWARD = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s ==> (c1092mcc_inward %s <=> c1092mais_northInward %s)"
    C1092AE_P C1092AE_HYP C1092MAIS_PK C1092MAIS_DOWN4 C1092AE_P),
  c1092mais_iff_tac [4]);;

(* Lean: half_north_ordinary *)
let C1092MAIS_HALF_NORTH_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s ==> (c1092mais_northOrdinary d1 d2 e1 e2 l <=> c1092mcc_ordinary %s)"
    C1092AE_P C1092AE_HYP C1092MAIS_PK C1092MAIS_OWN4),
  c1092mais_iff_tac [6]);;

(* Lean: half_north_inward *)
let C1092MAIS_HALF_NORTH_INWARD = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s ==> (c1092mais_northInward d1 d2 e1 e2 l <=> c1092mcc_inward %s)"
    C1092AE_P C1092AE_HYP C1092MAIS_PK C1092MAIS_OWN4),
  c1092mais_iff_tac [6]);;

(* Lean: north_cover *)
let C1092MAIS_NORTH_COVER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> c1092mais_northOrdinary %s \\/ c1092mais_northInward %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092AE_P C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_rot_tac "" 2 THEN
  SUBGOAL_THEN (parse_term C1092MAIS_PK) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092mais_halfTurn]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "") C1092MAIS_HALF_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MAIS_D5 C1092MANO_ORDINARY_OR_INWARD) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "") C1092MAIS_HALF_ORDINARY) THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "") C1092MAIS_HALF_INWARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;
