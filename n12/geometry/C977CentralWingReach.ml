(* ========================================================================= *)
(* Port of Compact/Bridge/C977CentralWingReach.lean                          *)
(* (N12Compact.C977CentralWingReach).  Two uniform central ownership         *)
(* implications in the original C977 family.  Conventions of                 *)
(* C977OppositeWallExtras.ml: p.square (orderedOwner p i) is c977wc_sq i,    *)
(* natCombinedOwners p (orderedOwner p i) is ooaux c1 c2 a b l (EL i         *)
(* c977av_code).  WingConditions is c977cwr_wing (v[i]! is EL i v),          *)
(* remainingVectors is c977cwr_remaining.  CentralWingReach.point_low:       *)
(* CWR_POINT_LOW; closed_of_inside (private): LINSIDE_CLOSED.  Tag C977CWR_. *)
(* ========================================================================= *)

needs "n12/geometry/CentralWingReach.ml";;
needs "n12/geometry/C977OppositeWallExtras.ml";;

(* Lean: forced_auxiliary (private) is C977WC_DOMAIN_CASES_TAC; apart (private) is
   C977CRC_APART-style NPACK_LDISJ via C977WC_LDISJ_TAC; closed_of_inside is LINSIDE_CLOSED *)

let c977cwr_pullx [c; s; u; v; a] =
  let neg t = mk_comb(`(--):real->real`, t)
  and sub x y = mk_binop `(-):real->real->real` x y
  and mul4 x = mk_binop `( * ):real->real->real` `&4` x in
  [neg c; s; sub u (mul4 c); sub (sub (neg v) a) (mul4 s); a];;

let c977cwr_pullsw [c; s; u; v; a] =
  [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a];;


let C977CWR_FINISH_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC LINSIDE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC) ORELSE
   (REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE
   ASM_REAL_ARITH_TAC);;

(* Lean: right_wing_point *)
let C977CWR_RIGHT_WING_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ 5 IN ooaux c1 c2 a b l (EL 6 c977av_code) ==> linside %s (&3) (&3 / &2)"
   C977WC_HYP (c977wc_sq 6)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&47 / &20) (&33 / &20) /\\ linside %s (&2) (&113 / &50) /\\
     linside %s (&3) (&87 / &50) /\\
     linside %s (&2) (&87 / &50) /\\ linside %s (&87 / &50) (&2)"
    (c977wc_sq 6) (c977wc_sq 6) (c977wc_sq 6) (c977wc_sq 5) (c977wc_sq 5))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 6 THEN ACCEPT_TAC(C977WC_INST (oo_seed 512 (`&47 / &20`, `&33 / &20`)));
      C977OWE_POINT_TAC 6 5;
      C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 8] THEN C977WC_DOMAIN_CASES_TAC 6;
      C977WC_TO_OO_TAC 5 THEN REWRITE_TAC[oo_aux_point 4] THEN C977WC_DOMAIN_CASES_TAC 5;
      C977WC_TO_OO_TAC 5 THEN REWRITE_TAC[oo_aux_point 13] THEN C977WC_DOMAIN_CASES_TAC 5];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 6) (c977wc_sq 5))) MP_TAC THENL
   [C977WC_LDISJ_TAC 6 5; REWRITE_TAC[ldisj] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 6`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 6 THEN C977WC_FACTS_TAC 5 THEN
  MP_TAC(SPECL (c977cwr_pullx (c977owc_comps 6) @ c977cwr_pullx (c977owc_comps 5)) CWR_POINT_LOW) THEN
  REWRITE_TAC[LINSIDE_PULLX; LCLOSED_PULLX; ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C977CWR_FINISH_TAC);;

(* Lean: right_wing *)
let C977CWR_RIGHT_WING = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     5 IN ooaux c1 c2 a b l (EL 6 c977av_code) ==> 18 IN ooaux c1 c2 a b l (EL 6 c977av_code)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CWR_RIGHT_WING_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&3) (&87 / &50)" (c977wc_sq 6))) ASSUME_TAC THENL
   [C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 8] THEN C977WC_DOMAIN_CASES_TAC 6; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&3) (&8 / &5)" (c977wc_sq 6))) MP_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
    C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 18; C977AV_CODE_EL.(6)]]);;

(* Lean: top_wing_point *)
let C977CWR_TOP_WING_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ 16 IN ooaux c1 c2 a b l (EL 7 c977av_code) ==> linside %s (&3 / &2) (&3)"
   C977WC_HYP (c977wc_sq 7)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&33 / &20) (&47 / &20) /\\ linside %s (&113 / &50) (&2) /\\
     linside %s (&87 / &50) (&3) /\\
     linside %s (&87 / &50) (&2) /\\ linside %s (&2) (&87 / &50)"
    (c977wc_sq 7) (c977wc_sq 7) (c977wc_sq 7) (c977wc_sq 5) (c977wc_sq 5))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 7 THEN ACCEPT_TAC(C977WC_INST (oo_seed 2048 (`&33 / &20`, `&47 / &20`)));
      C977OWE_POINT_TAC 7 16;
      C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 14] THEN C977WC_DOMAIN_CASES_TAC 7;
      C977WC_TO_OO_TAC 5 THEN REWRITE_TAC[oo_aux_point 13] THEN C977WC_DOMAIN_CASES_TAC 5;
      C977WC_TO_OO_TAC 5 THEN REWRITE_TAC[oo_aux_point 4] THEN C977WC_DOMAIN_CASES_TAC 5];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 7) (c977wc_sq 5))) MP_TAC THENL
   [C977WC_LDISJ_TAC 7 5; REWRITE_TAC[ldisj] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 7`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 7 THEN C977WC_FACTS_TAC 5 THEN
  MP_TAC(SPECL (c977cwr_pullx (c977cwr_pullsw (c977owc_comps 7)) @
                c977cwr_pullx (c977cwr_pullsw (c977owc_comps 5))) CWR_POINT_LOW) THEN
  REWRITE_TAC[LINSIDE_PULLX; LCLOSED_PULLX; LINSIDE_PULLSW; LCLOSED_PULLSW; ldisj] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C977CWR_FINISH_TAC);;

(* Lean: top_wing *)
let C977CWR_TOP_WING = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     16 IN ooaux c1 c2 a b l (EL 7 c977av_code) ==> 3 IN ooaux c1 c2 a b l (EL 7 c977av_code)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CWR_TOP_WING_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&87 / &50) (&3)" (c977wc_sq 7))) ASSUME_TAC THENL
   [C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 14] THEN C977WC_DOMAIN_CASES_TAC 7; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&8 / &5) (&3)" (c977wc_sq 7))) MP_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
    C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 3; C977AV_CODE_EL.(7)]]);;

(* Lean: WingConditions *)
let c977cwr_wing = new_definition
 `c977cwr_wing (v:(num->bool)list) <=>
    (5 IN EL 6 v ==> 18 IN EL 6 v) /\ (16 IN EL 7 v ==> 3 IN EL 7 v)`;;

(* Lean: actual_wing_conditions *)
let C977CWR_ACTUAL_WING_CONDITIONS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> c977cwr_wing (c977av_actual c1 c2 a b l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c977cwr_wing] THEN
  SIMP_TAC[C977AV_ACTUAL_AUXILIARY_SLOT; ARITH] THEN CONJ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC C977CWR_RIGHT_WING; MATCH_MP_TAC C977CWR_TOP_WING] THEN ASM_REWRITE_TAC[]);;

(* Lean: remainingVectors *)
let c977cwr_remaining = new_definition
 `c977cwr_remaining = FILTER c977cwr_wing c977owe_remaining`;;

let C977CWR_REMAINING_EXPLICIT =
  let cc = REWRITE_CONV[c977cwr_wing] THENC DEPTH_CONV EL_CONV THENC
           REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] in
  (REWRITE_CONV[c977cwr_remaining; C977OWE_REMAINING_EXPLICIT] THENC filter_by_conv cc)
  `c977cwr_remaining`;;

(* Lean: remaining_vector_count *)
let C977CWR_REMAINING_VECTOR_COUNT = prove
 (`LENGTH c977cwr_remaining = 50`,
  REWRITE_TAC[C977CWR_REMAINING_EXPLICIT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: canonical_remaining_cover *)
let C977CWR_CANONICAL_REMAINING_COVER = prove
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
      MEM (c977av_actual d1 d2 e1 e2 l) c977cwr_remaining`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977OWE_CANONICAL_REMAINING_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[c977cwr_remaining; MEM_FILTER] THEN
  MATCH_MP_TAC C977CWR_ACTUAL_WING_CONDITIONS THEN ASM_REWRITE_TAC[]);;
