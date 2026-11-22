(* ========================================================================= *)
(* Port of Compact/Bridge/C977BottomExtendedReach.lean                       *)
(* (N12Compact.C977BottomExtendedReach).  The original missing-corner        *)
(* strengthening pushes the actual bottom wall to (2.6,1).  Conventions of   *)
(* C977CentralReach.ml / C977WallCenters.ml (p.square (orderedOwner p i) is  *)
(* the 5-tuple c977wc_sq i).  WallStrongerLowerReach.point: WSLR_POINT;      *)
(* code_one_missing_points: C977MCP_CODE_ONE_MISSING_POINTS (horizontal_point *)
(* is the first conjunct of c977mcg_points).  Tag C977BER_.                  *)
(* ========================================================================= *)

needs "n12/geometry/WallStrongerLowerReach.ml";;
needs "n12/geometry/C977CentralReach.ml";;
needs "n12/geometry/MissingCornerPoints.ml";;
needs "n12/geometry/C977WallCenters.ml";;

(* Lean: point *)
let C977BER_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ ~linside %s (&1) (&1) ==> linside %s (&13 / &5) (&1)"
   C977WC_HYP (c977wc_sq 0) (c977wc_sq 9)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_BOTTOM_AUXILIARY) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C977WC_FACTS_TAC 0 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977MCP_CODE_ONE_MISSING_POINTS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_points] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 9) (c977wc_sq 0))) MP_TAC THENL
   [C977WC_LDISJ_TAC 9 0; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&91 / &50`; `&1`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 9) (c977wc_sq 5))) MP_TAC THENL
   [C977WC_LDISJ_TAC 9 5; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&3 / &2`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 9 THEN
  ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN
  MATCH_MP_TAC WSLR_POINT THEN ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCONT_PULLSW THEN C977WC_TO_OO_TAC 9 THEN ASM_SIMP_TAC[OO_BOX]; ALL_TAC] THEN
  C977WC_TO_OO_TAC 9 THEN
  ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`))));;
