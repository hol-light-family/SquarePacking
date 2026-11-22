(* ========================================================================= *)
(* Port of Compact/Bridge/C977OppositeWallCenters.lean                       *)
(* (N12Compact.C977OppositeWallCenters).  Both opposite-wall centers lie     *)
(* above their midpoint splits.  Conventions of C977WallCenters.ml           *)
(* (p.square (orderedOwner p i) is the 5-tuple c977wc_sq i; OppositeWallBranch*)
(* is bool#bool, expandWallBranch is c977wc_expand).  pullX q is the 5-tuple  *)
(* of LINSIDE_PULLX, pullSwap that of LINSIDE_PULLSW.                         *)
(* WallLowerCenterBarrier.center_above: WLCB_CENTER_ABOVE; unused_marker_ten:*)
(* C977WB_UNUSED_MARKER_TEN.  Tag C977OWC_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/WallLowerCenterBarrier.ml";;
needs "n12/geometry/C977WallCenters.ml";;

let c977owc_comps i =
  let w = Printf.sprintf "(c977av_ordered_owner c1 c2 a b l %d)" i in
  map parse_term
   [Printf.sprintf "(a:num->real) %s" w; Printf.sprintf "(b:num->real) %s" w;
    Printf.sprintf "a %s * c1 %s + b %s * (c2:num->real) %s - l / &2" w w w w;
    Printf.sprintf "--b %s * c1 %s + a %s * (c2:num->real) %s - l / &2" w w w w; "l:real"];;

(* Lean: forced_auxiliary (private) *)
let C977OWC_FORCED_AUXILIARY = prove
 (`forall c1 c2 a b l i n. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ (forall os. MEM os (EL i c977av_prune4) ==> n IN os)
     ==> n IN ooaux c1 c2 a b l (EL i c977av_code)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977AV_PRUNED_AUXILIARY_DOMAIN_ACTUAL) THEN
  ASM_SIMP_TAC[]);;

(* Lean: apart (private) is C977WC_DISTINCT *)

let C977OWC_LCY_PULLX = prove
 (`forall c s u v a. lcy (--c) s (u - &4 * c) (--v - a - &4 * s) a = lcy c s u v a`,
  REWRITE_TAC[lcy] THEN REAL_ARITH_TAC);;

let C977OWC_LCY_PULLSW = prove
 (`forall c s u v a. lcy s c u (--v - a) a = lcx c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

let C977OWC_MARKER10 = prove
 (`marker 10$1 = &47 / &20 /\ marker 10$2 = &47 / &20`,
  REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: right_center *)
let C977OWC_RIGHT_CENTER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> &21 / &10 < lcy %s" C977WC_HYP (c977wc_sq 10)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1543 / &500) (&2) /\\ linside %s (&3) (&12 / &5) /\\ linside %s (&3) (&87 / &50)"
    (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 6))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 10 THEN ACCEPT_TAC(C977WC_INST (oo_seed 16384 (`&1543 / &500`, `&2`)));
      C977WC_TO_OO_TAC 10 THEN REWRITE_TAC[oo_aux_point 19] THEN C977WC_DOMAIN_CASES_TAC 10;
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
                  (mk_binop `( * ):real->real->real` `&4` sq); aq] WLCB_CENTER_ABOVE) THEN
  REWRITE_TAC[LINSIDE_PULLX; C977OWC_LCY_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LCONT_PULLX THEN C977WC_TO_OO_TAC 10 THEN ASM_SIMP_TAC[OO_BOX]);;

(* Lean: top_center *)
let C977OWC_TOP_CENTER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> &21 / &10 < lcx %s" C977WC_HYP (c977wc_sq 11)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&2) (&1543 / &500) /\\ linside %s (&12 / &5) (&3) /\\ linside %s (&87 / &50) (&3)"
    (c977wc_sq 11) (c977wc_sq 11) (c977wc_sq 7))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 11 THEN ACCEPT_TAC(C977WC_INST (oo_seed 32768 (`&2`, `&1543 / &500`)));
      C977WC_TO_OO_TAC 11 THEN REWRITE_TAC[oo_aux_point 7] THEN C977WC_DOMAIN_CASES_TAC 11;
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
                  (mk_binop `( * ):real->real->real` `&4` cq); aq] WLCB_CENTER_ABOVE) THEN
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLSW; C977OWC_LCY_PULLX; C977OWC_LCY_PULLSW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LCONT_PULLX THEN MATCH_MP_TAC LCONT_PULLSW THEN
  C977WC_TO_OO_TAC 11 THEN ASM_SIMP_TAC[OO_BOX]);;

(* Lean: opposite_branch_restriction *)
let C977OWC_OPPOSITE_BRANCH_RESTRICTION = prove
 (`forall c1 c2 a b l w bp.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     c977wb_owners c1 c2 a b l w /\ c977wb_half c1 c2 a b l w (c977wc_expand bp)
     ==> bp = (false,false)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `w 2 = c977av_ordered_owner c1 c2 a b l 10 /\ w 3 = c977av_ordered_owner c1 c2 a b l 11`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OWNMASK_INJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
    ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN REWRITE_TAC[GSYM c977av_ordered_owner] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[c977wb_owners] o
      check (can (term_match [] `c977wb_owners c1 c2 a b l w`) o concl)) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
    REWRITE_TAC[ARITH; C977WB_WALLCODE_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
      C977AV_ORDERED_OWNER_CODE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[ARITH] (SPEC `10` th);
                                                            REWRITE_RULE[ARITH] (SPEC `11` th)]) THEN
    REWRITE_TAC[C977AV_CODE_EL.(10); C977AV_CODE_EL.(11)];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977OWC_RIGHT_CENTER) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977OWC_TOP_CENTER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c977wb_half; c977wc_expand] o
    check (can (term_match [] `c977wb_half c1 c2 a b l w bb`) o concl)) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH; c977wb_coord] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM PAIR] THEN REWRITE_TAC[PAIR_EQ; FST; SND] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

let C977OWC_COVER_BODY =
 `((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
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
      exists v. v < LENGTH c977av_vectors /\ c977wb_half d1 d2 e1 e2 l w (c977wc_expand (false,false)) /\
             EL v c977av_vectors = c977av_actual d1 d2 e1 e2 l`;;

(* Lean: canonical_single_wall_context_cover *)
let C977OWC_CANONICAL_SINGLE_WALL_CONTEXT_COVER = prove
 (mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`, mk_forall(`b:num->real`,
  mk_forall(`l:real`, mk_imp(
   `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`,
   list_mk_exists([`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`], C977OWC_COVER_BODY))))))),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977WC_CANONICAL_FOUR_WALL_CONTEXT_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:num` THEN
  UNDISCH_TAC `(bp:bool#bool,v:num) IN c977wc_rindex` THEN
  REWRITE_TAC[c977wc_rindex; IN_ELIM_PAIR_THM; IN_UNIV] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`;
                `w:num->num`; `bp:bool#bool`] C977OWC_OPPOSITE_BRANCH_RESTRICTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_of_single_wall_contexts *)
let C977OWC_EXCLUDES_CASE_OF_SINGLE_WALL_CONTEXTS = prove
 (`(forall c1 c2 a b l.
      NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
      c977mcp_strengthened (a (c977av_ordered_owner c1 c2 a b l 0)) (b (c977av_ordered_owner c1 c2 a b l 0))
        (a (c977av_ordered_owner c1 c2 a b l 0) * c1 (c977av_ordered_owner c1 c2 a b l 0) +
         b (c977av_ordered_owner c1 c2 a b l 0) * c2 (c977av_ordered_owner c1 c2 a b l 0) - l / &2)
        (--b (c977av_ordered_owner c1 c2 a b l 0) * c1 (c977av_ordered_owner c1 c2 a b l 0) +
         a (c977av_ordered_owner c1 c2 a b l 0) * c2 (c977av_ordered_owner c1 c2 a b l 0) - l / &2) l /\
      c977mcb_ccb (a (c977av_ordered_owner c1 c2 a b l 0)) (b (c977av_ordered_owner c1 c2 a b l 0))
        (a (c977av_ordered_owner c1 c2 a b l 0) * c1 (c977av_ordered_owner c1 c2 a b l 0) +
         b (c977av_ordered_owner c1 c2 a b l 0) * c2 (c977av_ordered_owner c1 c2 a b l 0) - l / &2)
        (--b (c977av_ordered_owner c1 c2 a b l 0) * c1 (c977av_ordered_owner c1 c2 a b l 0) +
         a (c977av_ordered_owner c1 c2 a b l 0) * c2 (c977av_ordered_owner c1 c2 a b l 0) - l / &2) l
      ==> forall w v. c977wb_owners c1 c2 a b l w /\ v < LENGTH c977av_vectors /\
                c977wb_half c1 c2 a b l w (c977wc_expand (false,false)) /\
                EL v c977av_vectors = c977av_actual c1 c2 a b l ==> false)
   ==> excl_case 977`,
  DISCH_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977OWC_CANONICAL_SINGLE_WALL_CONTEXT_COVER) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`w:num->num`; `v:num`]) THEN
  ASM_REWRITE_TAC[]);;
