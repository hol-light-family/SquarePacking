(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOrdinaryWallAdvance.lean             *)
(* (N12Compact.C1092MPPMOrdinaryWallAdvance; Lean header: "This source has   *)
(* not been compiled or replayed").  An ordinary central point removes the   *)
(* adjacent wall's inward auxiliary; WallLowerReach.point (WLR_POINT) then   *)
(* gives a strict far point in the same actual wall.  Conventions of         *)
(* CP_C1092_MPPMEntrance.ml / CP_C1092_MPPMOmissions.ml (owners p i at mask  *)
(* EL i c1092wc_code, side l; WallContext p mppm is                          *)
(* c1092wc_ctx c1 c2 a b l c1092mppe_mppm; Missing is c1092mom_missing).     *)
(* OrdinaryCentralReduction.*_inner_absent: C1092OCR_*_INNER_ABSENT.  The    *)
(* charts pullSwap (pullX q), pullY (pullX q), pullSwap (pullY q) are built  *)
(* with the c1092mo_ layer toolkit (CP_C1092_MMMP_Origins.ml; only NPACK /   *)
(* IMAGE are used); container_pull* via c1092mo_plcont.                      *)
(* OriginalOwners.horizontal_segment is OO_HORIZONTAL_SEGMENT.               *)
(* Tag C1092OWA_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_OrdinaryCentralReduction.ml";;
needs "n12/geometry/CP_C1092_MPPMOmissions.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/CP_C1092_MMMP_Origins.ml";;

(* Lean: side_gt (private) *)
let C1092OWA_SIDE_GT = C1092MPPE_SIDE_GT;;

(* Lean: marker_point (private): markers are oo_seed points (c1092mo_seed) *)

let C1092OWA_NP = `NPACK c1 c2 a b l`;;
let C1092OWA_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`;;
let C1092OWA_CTX = parse_term C1092MPPE_CTX;;
let c1092owa_lit s = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term s));;
(* an EL-form theorem with hyps NPACK /\ IMAGE /\ CTX /\ h1 /\ h2, in literal form *)
let c1092owa_use th hs =
  CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th)
    (end_itlist CONJ ([ASSUME C1092OWA_NP; ASSUME C1092OWA_IMG; ASSUME C1092OWA_CTX] @
                      map (fun s -> ASSUME (parse_term s)) hs)));;
(* WallLowerReach.point in the chart [layers] of wall owner wi *)
let c1092owa_reach wi layers mark g excl missing =
  let t, eqs = c1092mo_layers wi layers in
  c1092mo_apply (c1092mo_conv eqs) (SPECL t WLR_POINT)
    [c1092mo_punit wi t; c1092mo_side (); c1092mo_plcont wi layers; c1092mo_seed wi mark;
     g; excl; missing];;
let c1092owa_close hs concl th =
  prove(parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX
          (String.concat " /\\ " hs) concl),
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN ACCEPT_TAC th);;

let C1092OWA_LEFTG = c1092mppe_in 8 "&1" "&12 / &5";;
let C1092OWA_BOTTOMF = c1092mppe_in 9 "&8 / &5" "&1";;
let C1092OWA_RIGHTG = c1092mppe_in 10 "&3" "&8 / &5";;
let C1092OWA_TOPF = c1092mppe_in 11 "&12 / &5" "&3";;
let C1092OWA_CF0 = c1092mppe_in 4 "&1" "&87 / &50";;
let C1092OWA_CG5 = c1092mppe_in 5 "&113 / &50" "&1";;
let C1092OWA_CF9 = c1092mppe_in 6 "&3" "&113 / &50";;
let C1092OWA_CG4 = c1092mppe_in 7 "&87 / &50" "&3";;

(* Lean: left_far *)
let C1092OWA_LEFT_FAR = c1092owa_close [C1092OWA_LEFTG; C1092OWA_BOTTOMF; C1092OWA_CF0]
  (c1092mppe_in 8 "&1" "&64 / &25")
  (c1092owa_reach 8 [] (`&457 / &500`, `&2`) (c1092owa_lit C1092OWA_LEFTG)
     (c1092mo_excl 8 4 (c1092owa_lit C1092OWA_CF0))
     (c1092owa_use C1092OCR_LEFT_INNER_ABSENT [C1092OWA_BOTTOMF; C1092OWA_CF0]));;

(* Lean: bottom_far *)
let C1092OWA_BOTTOM_FAR = c1092owa_close [C1092OWA_BOTTOMF; C1092OWA_RIGHTG; C1092OWA_CG5]
  (c1092mppe_in 9 "&36 / &25" "&1")
  (c1092owa_reach 9 [C1092MO_X; C1092MO_SW] (`&2`, `&457 / &500`) (c1092owa_lit C1092OWA_BOTTOMF)
     (c1092mo_excl 9 5 (c1092owa_lit C1092OWA_CG5))
     (c1092owa_use C1092OCR_BOTTOM_INNER_ABSENT [C1092OWA_RIGHTG; C1092OWA_CG5]));;

(* Lean: right_far *)
let C1092OWA_RIGHT_FAR = c1092owa_close [C1092OWA_RIGHTG; C1092OWA_TOPF; C1092OWA_CF9]
  (c1092mppe_in 10 "&3" "&36 / &25")
  (c1092owa_reach 10 [C1092MO_X; C1092MO_Y] (`&1543 / &500`, `&2`) (c1092owa_lit C1092OWA_RIGHTG)
     (c1092mo_excl 10 6 (c1092owa_lit C1092OWA_CF9))
     (c1092owa_use C1092OCR_RIGHT_INNER_ABSENT [C1092OWA_TOPF; C1092OWA_CF9]));;

(* Lean: top_far *)
let C1092OWA_TOP_FAR = c1092owa_close [C1092OWA_TOPF; C1092OWA_LEFTG; C1092OWA_CG4]
  (c1092mppe_in 11 "&64 / &25" "&3")
  (c1092owa_reach 11 [C1092MO_Y; C1092MO_SW] (`&2`, `&1543 / &500`) (c1092owa_lit C1092OWA_TOPF)
     (c1092mo_excl 11 7 (c1092owa_lit C1092OWA_CG4))
     (c1092owa_use C1092OCR_TOP_INNER_ABSENT [C1092OWA_LEFTG; C1092OWA_CG4]));;

let C1092OWA_EMPTY = "(!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k)";;
let c1092owa_no_omission central concl far =
  prove(parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX
          C1092OWA_EMPTY central concl),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL C1092MOM_ORDINARY_WALLS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC far THEN ASM_REWRITE_TAC[]);;

(* Lean: bottom_far_no_omission *)
let C1092OWA_BOTTOM_FAR_NO_OMISSION = c1092owa_no_omission C1092OWA_CG5
  (c1092mppe_in 9 "&36 / &25" "&1") C1092OWA_BOTTOM_FAR;;

(* Lean: left_far_no_omission *)
let C1092OWA_LEFT_FAR_NO_OMISSION = c1092owa_no_omission C1092OWA_CF0
  (c1092mppe_in 8 "&1" "&64 / &25") C1092OWA_LEFT_FAR;;

(* Lean: right_far_no_omission *)
let C1092OWA_RIGHT_FAR_NO_OMISSION = c1092owa_no_omission C1092OWA_CF9
  (c1092mppe_in 10 "&3" "&36 / &25") C1092OWA_RIGHT_FAR;;

(* Lean: top_far_no_omission *)
let C1092OWA_TOP_FAR_NO_OMISSION = c1092owa_no_omission C1092OWA_CG4
  (c1092mppe_in 11 "&64 / &25" "&3") C1092OWA_TOP_FAR;;

(* Lean: all_far_no_omission *)
let C1092OWA_ALL_FAR_NO_OMISSION = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ %s ==> %s /\\ %s /\\ %s /\\ %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092OWA_EMPTY
    C1092OWA_CF0 C1092OWA_CG5 C1092OWA_CF9 C1092OWA_CG4
    (c1092mppe_in 8 "&1" "&64 / &25") (c1092mppe_in 9 "&36 / &25" "&1")
    (c1092mppe_in 10 "&3" "&36 / &25") (c1092mppe_in 11 "&64 / &25" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [C1092OWA_LEFT_FAR_NO_OMISSION; C1092OWA_BOTTOM_FAR_NO_OMISSION;
     C1092OWA_RIGHT_FAR_NO_OMISSION; C1092OWA_TOP_FAR_NO_OMISSION]));;

(* Lean: bottom_bar_no_omission *)
let C1092OWA_BOTTOM_BAR_NO_OMISSION = prove
 (parse_term (Printf.sprintf "!%s x. %s /\\ %s /\\ %s /\\ %s /\\ &36 / &25 <= x /\\ x <= &87 / &50 ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092OWA_EMPTY C1092OWA_CG5 (c1092mppe_in 9 "x" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092OWA_BOTTOM_FAR_NO_OMISSION) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MPPE_WALL_AUXILIARIES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&36 / &25`; `&87 / &50`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
