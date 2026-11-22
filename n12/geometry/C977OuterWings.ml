(* ========================================================================= *)
(* Port of Compact/Bridge/C977OuterWings.lean (N12Compact.C977OuterWings).   *)
(* Both outer wing points have unique, uniform central owners in C977.       *)
(* Conventions of C977CentralWingReach.ml: p.square (orderedOwner p i) is    *)
(* c977wc_sq i, natCombinedOwners p (orderedOwner p i) is ooaux c1 c2 a b l  *)
(* (EL i c977av_code).  OuterConditions is c977ow_outer (v[i]! is EL i v),   *)
(* remainingVectors is c977ow_remaining.  CentralOuterWing.point: COW_POINT. *)
(* Tag C977OW_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CentralOuterWing.ml";;
needs "n12/geometry/C977CentralReach.ml";;
needs "n12/geometry/C977CentralWingReach.ml";;

(* Lean: forced (private) is C977WC_DOMAIN_CASES_TAC; apart (private) is C977WC_LDISJ_TAC *)

(* Lean: top_of_inner *)
let C977OW_TOP_OF_INNER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ 5 IN ooaux c1 c2 a b l (EL 7 c977av_code) ==> linside %s (&8 / &5) (&3)"
   C977WC_HYP (c977wc_sq 7)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&33 / &20) (&47 / &20) /\\ linside %s (&2) (&113 / &50) /\\
     linside %s (&87 / &50) (&3)"
    (c977wc_sq 7) (c977wc_sq 7) (c977wc_sq 7))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 7 THEN ACCEPT_TAC(C977WC_INST (oo_seed 2048 (`&33 / &20`, `&47 / &20`)));
      C977OWE_POINT_TAC 7 5;
      C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 14] THEN C977WC_DOMAIN_CASES_TAC 7];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 7) (c977wc_sq 5))) MP_TAC THENL
   [C977WC_LDISJ_TAC 7 5;
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&3 / &2`; `&2`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 7`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 7 THEN
  MP_TAC(SPECL (c977owc_comps 7) COW_POINT) THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: right_of_inner *)
let C977OW_RIGHT_OF_INNER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ 16 IN ooaux c1 c2 a b l (EL 6 c977av_code) ==> linside %s (&3) (&8 / &5)"
   C977WC_HYP (c977wc_sq 6)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&47 / &20) (&33 / &20) /\\ linside %s (&113 / &50) (&2) /\\
     linside %s (&3) (&87 / &50)"
    (c977wc_sq 6) (c977wc_sq 6) (c977wc_sq 6))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 6 THEN ACCEPT_TAC(C977WC_INST (oo_seed 512 (`&47 / &20`, `&33 / &20`)));
      C977OWE_POINT_TAC 6 16;
      C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 8] THEN C977WC_DOMAIN_CASES_TAC 6];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 6) (c977wc_sq 5))) MP_TAC THENL
   [C977WC_LDISJ_TAC 6 5;
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&3 / &2`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 6`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 6 THEN
  MP_TAC(SPECL (c977cwr_pullsw (c977owc_comps 6)) COW_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: owned *)
let C977OW_OWNED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> 18 IN ooaux c1 c2 a b l (EL 6 c977av_code) /\ 3 IN ooaux c1 c2 a b l (EL 7 c977av_code)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_CASES_TAC `16 IN ooaux c1 c2 a b l (EL 6 c977av_code)` THENL
     [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
        C977OW_RIGHT_OF_INNER) THEN ASM_REWRITE_TAC[] THEN
      C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 18; C977AV_CODE_EL.(6)];
      POP_ASSUM MP_TAC THEN REWRITE_TAC[C977AV_CODE_EL.(6)] THEN
      C977WC_DOMAIN_CASES_TAC 6];
    ASM_CASES_TAC `5 IN ooaux c1 c2 a b l (EL 7 c977av_code)` THENL
     [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
        C977OW_TOP_OF_INNER) THEN ASM_REWRITE_TAC[] THEN
      C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 3; C977AV_CODE_EL.(7)];
      POP_ASSUM MP_TAC THEN REWRITE_TAC[C977AV_CODE_EL.(7)] THEN
      C977WC_DOMAIN_CASES_TAC 7]]);;

(* Lean: points *)
let C977OW_POINTS = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s ==> linside %s (&3) (&8 / &5) /\\ linside %s (&8 / &5) (&3)"
   C977WC_HYP (c977wc_sq 6) (c977wc_sq 7)),
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(MATCH_MP C977OW_OWNED th)) THEN
  C977WC_TO_OO_TAC 6 THEN C977WC_TO_OO_TAC 7 THEN
  REWRITE_TAC[oo_aux_point 18; oo_aux_point 3; C977AV_CODE_EL.(6); C977AV_CODE_EL.(7)]);;

(* Lean: OuterConditions *)
let c977ow_outer = new_definition
 `c977ow_outer (v:(num->bool)list) <=> 18 IN EL 6 v /\ 3 IN EL 7 v`;;

(* Lean: actual_outer_conditions *)
let C977OW_ACTUAL_OUTER_CONDITIONS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> c977ow_outer (c977av_actual c1 c2 a b l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[c977ow_outer] THEN
  SIMP_TAC[C977AV_ACTUAL_AUXILIARY_SLOT; ARITH] THEN
  MATCH_MP_TAC C977OW_OWNED THEN ASM_REWRITE_TAC[]);;

(* Lean: remainingVectors *)
let c977ow_remaining = new_definition
 `c977ow_remaining = FILTER c977ow_outer c977cwr_remaining`;;

(* Lean: canonical_remaining_cover *)
let C977OW_CANONICAL_REMAINING_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
   ==> exists d1 d2 e1 e2.
  ((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
  NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\
  c977mcp_strengthened (e1 (c977av_ordered_owner d1 d2 e1 e2 l 0)) (e2 (c977av_ordered_owner d1 d2 e1 e2 l 0))
    (e1 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d1 (c977av_ordered_owner d1 d2 e1 e2 l 0) +
     e2 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d2 (c977av_ordered_owner d1 d2 e1 e2 l 0) - l / &2)
    (--e2 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d1 (c977av_ordered_owner d1 d2 e1 e2 l 0) +
     e1 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d2 (c977av_ordered_owner d1 d2 e1 e2 l 0) - l / &2) l /\
  c977mcb_ccb (e1 (c977av_ordered_owner d1 d2 e1 e2 l 0)) (e2 (c977av_ordered_owner d1 d2 e1 e2 l 0))
    (e1 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d1 (c977av_ordered_owner d1 d2 e1 e2 l 0) +
     e2 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d2 (c977av_ordered_owner d1 d2 e1 e2 l 0) - l / &2)
    (--e2 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d1 (c977av_ordered_owner d1 d2 e1 e2 l 0) +
     e1 (c977av_ordered_owner d1 d2 e1 e2 l 0) * d2 (c977av_ordered_owner d1 d2 e1 e2 l 0) - l / &2) l /\
  exists w. c977wb_owners d1 d2 e1 e2 l w /\
      c977wb_half d1 d2 e1 e2 l w (c977wc_expand (false,false)) /\
      MEM (c977av_actual d1 d2 e1 e2 l) c977ow_remaining`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977CWR_CANONICAL_REMAINING_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[c977ow_remaining; MEM_FILTER] THEN
  MATCH_MP_TAC C977OW_ACTUAL_OUTER_CONDITIONS THEN ASM_REWRITE_TAC[]);;
