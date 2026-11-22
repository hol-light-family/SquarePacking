(* ========================================================================= *)
(* Port of Compact/Bridge/C977OppositeWallExtras.lean                        *)
(* (N12Compact.C977OppositeWallExtras).  The two opposite wall owners cannot *)
(* both own their inward extra point; this excludes one complete C977 vector.*)
(* Conventions of C977WallCenters.ml / C977OppositeWallCenters.ml:           *)
(* p.square (orderedOwner p i) is the 5-tuple c977wc_sq i;                   *)
(* natCombinedOwners p (orderedOwner p i) is ooaux c1 c2 a b l (EL i         *)
(* c977av_code) (as in C977OWC_FORCED_AUXILIARY).  excludedVector is         *)
(* c977owe_excluded, remainingVectors c977owe_remaining.                     *)
(* WallInwardCenter.center_box: WIC_CENTER_BOX; border_packing_center_       *)
(* distance: C977BP_BORDER_PACKING_CENTER_DISTANCE.  Tag C977OWE_.           *)
(* ========================================================================= *)

needs "n12/geometry/WallInwardCenter.ml";;
needs "n12/geometry/C977OppositeWallCenters.ml";;
needs "n12/geometry/BorderPoints.ml";;

(* Lean: forced_auxiliary (private) is C977OWC_FORCED_AUXILIARY / C977WC_DOMAIN_CASES_TAC;
   apart (private) is C977WC_DISTINCT *)

let C977OWE_LCX_PULLX = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcx (--c) s (u - &4 * c) (--v - a - &4 * s) a = &4 - lcx c s u v a`,
  REWRITE_TAC[lcx] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let C977OWE_LCX_PULLSW = prove
 (`forall c s u v a. lcx s c u (--v - a) a = lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* the inward extra point (113/50, 2) of slot 10 / (2, 113/50) of slot 11 *)
let C977OWE_POINT_TAC i n =
  C977WC_TO_OO_TAC i THEN REWRITE_TAC[oo_aux_point n] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C977AV_CODE_EL.(i)]) THEN ASM_REWRITE_TAC[];;

(* Lean: right_box (private) *)
let C977OWE_RIGHT_BOX = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ 16 IN ooaux c1 c2 a b l (EL 10 c977av_code)
     ==> &9 / &4 <= lcx %s /\\ lcx %s <= &59 / &20 /\\ &9 / &4 <= lcy %s /\\ lcy %s <= &59 / &20"
   C977WC_HYP (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 10)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1543 / &500) (&2) /\\ linside %s (&3) (&12 / &5) /\\ linside %s (&113 / &50) (&2) /\\
     linside %s (&3) (&87 / &50)"
    (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 6))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 10 THEN ACCEPT_TAC(C977WC_INST (oo_seed 16384 (`&1543 / &500`, `&2`)));
      C977WC_TO_OO_TAC 10 THEN REWRITE_TAC[oo_aux_point 19] THEN C977WC_DOMAIN_CASES_TAC 10;
      C977OWE_POINT_TAC 10 16;
      C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 8] THEN C977WC_DOMAIN_CASES_TAC 6];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 10) (c977wc_sq 6))) MP_TAC THENL
   [C977WC_LDISJ_TAC 10 6; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&3`; `&87 / &50`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 10`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 10 THEN
  let [cq; sq; uq; vq; aq] = c977owc_comps 10 in
  MP_TAC(SPECL [mk_comb(`(--):real->real`, cq); sq; mk_binop `(-):real->real->real` uq (mk_binop `( * ):real->real->real` `&4` cq);
                mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, vq)) aq)
                  (mk_binop `( * ):real->real->real` `&4` sq); aq] WIC_CENTER_BOX) THEN
  ASM_SIMP_TAC[LINSIDE_PULLX; C977OWC_LCY_PULLX; C977OWE_LCX_PULLX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] ORELSE ALL_TAC) THEN
  REAL_ARITH_TAC);;

(* Lean: top_box (private) *)
let C977OWE_TOP_BOX = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ 5 IN ooaux c1 c2 a b l (EL 11 c977av_code)
     ==> &9 / &4 <= lcx %s /\\ lcx %s <= &59 / &20 /\\ &9 / &4 <= lcy %s /\\ lcy %s <= &59 / &20"
   C977WC_HYP (c977wc_sq 11) (c977wc_sq 11) (c977wc_sq 11) (c977wc_sq 11)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&2) (&1543 / &500) /\\ linside %s (&12 / &5) (&3) /\\ linside %s (&2) (&113 / &50) /\\
     linside %s (&87 / &50) (&3)"
    (c977wc_sq 11) (c977wc_sq 11) (c977wc_sq 11) (c977wc_sq 7))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 11 THEN ACCEPT_TAC(C977WC_INST (oo_seed 32768 (`&2`, `&1543 / &500`)));
      C977WC_TO_OO_TAC 11 THEN REWRITE_TAC[oo_aux_point 7] THEN C977WC_DOMAIN_CASES_TAC 11;
      C977OWE_POINT_TAC 11 5;
      C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 14] THEN C977WC_DOMAIN_CASES_TAC 7];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 11) (c977wc_sq 7))) MP_TAC THENL
   [C977WC_LDISJ_TAC 11 7; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&87 / &50`; `&3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 11`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 11 THEN
  let [cq; sq; uq; vq; aq] = c977owc_comps 11 in
  (* pullSwap q = (sq, cq, uq, --vq - aq, aq); then pullX *)
  let vs = mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, vq)) aq in
  MP_TAC(SPECL [mk_comb(`(--):real->real`, sq); cq; mk_binop `(-):real->real->real` uq (mk_binop `( * ):real->real->real` `&4` sq);
                mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, vs)) aq)
                  (mk_binop `( * ):real->real->real` `&4` cq); aq] WIC_CENTER_BOX) THEN
  SUBGOAL_THEN (mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` sq sq)
                        (mk_binop `( * ):real->real->real` cq cq), `&1`)) ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LINSIDE_PULLX; LINSIDE_PULLSW; C977OWC_LCY_PULLX; C977OWC_LCY_PULLSW;
               C977OWE_LCX_PULLX; C977OWE_LCX_PULLSW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] ORELSE ALL_TAC) THEN
  REAL_ARITH_TAC);;

let C977OWE_DIAMETER = prove
 (`forall xr yr xt yt. &9 / &4 <= xr /\ xr <= &59 / &20 /\ &9 / &4 <= yr /\ yr <= &59 / &20 /\
                 &9 / &4 <= xt /\ xt <= &59 / &20 /\ &9 / &4 <= yt /\ yt <= &59 / &20
                 ==> &1 < (xt - xr) pow 2 + (yt - yr) pow 2 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(xt - xr) pow 2 <= (&7 / &10) pow 2 /\ (yt - yr) pow 2 <= (&7 / &10) pow 2` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* Lean: simultaneous_extras_impossible *)
let C977OWE_SIMULTANEOUS_EXTRAS_IMPOSSIBLE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     16 IN ooaux c1 c2 a b l (EL 10 c977av_code) /\ 5 IN ooaux c1 c2 a b l (EL 11 c977av_code)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977OWE_RIGHT_BOX) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977OWE_TOP_BOX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 10`; `c977av_ordered_owner c1 c2 a b l 11`]
    C977BP_BORDER_PACKING_CENTER_DISTANCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN REWRITE_TAC[GSYM c977av_ordered_owner] THEN
    MATCH_MP_TAC C977WC_DISTINCT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC C977OWE_DIAMETER THEN ASM_REWRITE_TAC[]);;

(* Lean: excludedVector *)
let c977owe_excluded = new_definition
 `c977owe_excluded : (num->bool)list =
    [{2,12}; {0,10}; {}; {}; {}; {4,13}; {8,18}; {3,14}; {1,11}; {6,15}; {9,16,19}; {5,7,17}]`;;

(* Lean: excluded_vector_present *)
let C977OWE_EXCLUDED_VECTOR_PRESENT = prove
 (`MEM c977owe_excluded c977av_vectors`,
  REWRITE_TAC[C977AV_VECTORS_EXPLICIT; c977owe_excluded; MEM; CONS_11] THEN
  CONV_TAC(ONCE_DEPTH_CONV setlit_eq_dconv) THEN REWRITE_TAC[]);;

(* Lean: extra_pair_vector_unique  (v[10]! is EL 10 v; all vectors have length 12) *)
let C977OWE_EXTRA_PAIR_VECTOR_UNIQUE = prove
 (`forall v. MEM v c977av_vectors ==> 16 IN EL 10 v ==> 5 IN EL 11 v ==> v = c977owe_excluded`,
  GEN_TAC THEN REWRITE_TAC[C977AV_VECTORS_EXPLICIT; MEM] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[c977owe_excluded; CONS_11] THEN
  CONV_TAC(ONCE_DEPTH_CONV setlit_eq_dconv) THEN REWRITE_TAC[]);;

(* Lean: actual_not_excluded *)
let C977OWE_ACTUAL_NOT_EXCLUDED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> ~(c977av_actual c1 c2 a b l = c977owe_excluded)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977OWE_SIMULTANEOUS_EXTRAS_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[ARITH] (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
     `b:num->real`; `l:real`; `10`] C977AV_ACTUAL_AUXILIARY_SLOT));
              GSYM(REWRITE_RULE[ARITH] (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
     `b:num->real`; `l:real`; `11`] C977AV_ACTUAL_AUXILIARY_SLOT))] THEN
  ASM_REWRITE_TAC[c977owe_excluded] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[IN_INSERT] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: remainingVectors *)
let c977owe_remaining = new_definition
 `c977owe_remaining = FILTER (\v. ~(v = c977owe_excluded)) c977av_vectors`;;

let C977OWE_REMAINING_EXPLICIT =
  (REWRITE_CONV[c977owe_remaining; C977AV_VECTORS_EXPLICIT; c977owe_excluded] THENC
   filter_eval_conv (fun t -> (REWRITE_CONV[CONS_11] THENC ONCE_DEPTH_CONV setlit_eq_dconv THENC
                               REWRITE_CONV[]) t))
  `c977owe_remaining`;;

(* Lean: remaining_vector_count *)
let C977OWE_REMAINING_VECTOR_COUNT = prove
 (`LENGTH c977owe_remaining = 56`,
  REWRITE_TAC[C977OWE_REMAINING_EXPLICIT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: canonical_remaining_cover *)
let C977OWE_CANONICAL_REMAINING_COVER = prove
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
      MEM (c977av_actual d1 d2 e1 e2 l) c977owe_remaining`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977OWC_CANONICAL_SINGLE_WALL_CONTEXT_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[c977owe_remaining; MEM_FILTER] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONJ_TAC THEN
  FIRST [MATCH_MP_TAC C977OWE_ACTUAL_NOT_EXCLUDED; MATCH_MP_TAC C977AV_ACTUAL_AUXILIARY_VECTOR_MEM] THEN
  ASM_REWRITE_TAC[]);;
