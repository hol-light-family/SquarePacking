(* ========================================================================= *)
(* Port of Compact/Bridge/C977WallCenters.lean (N12Compact.C977WallCenters). *)
(* Case 977 loses twelve wall branches uniformly over all 57 vectors.        *)
(* Conventions of AuxiliaryContext.ml / AuxiliaryVectors.ml / WallBranches:  *)
(* orderedOwner p i is c977av_ordered_owner c1 c2 a b l i; the owner of      *)
(* mask EL i c977av_code is the OriginalOwners tuple (ooc .. m);  a          *)
(* WallBranch b is bb : num->bool (b k = false is ~bb k); OppositeWallBranch *)
(* = Bool x Bool is bool#bool; expandWallBranch is c977wc_expand (canonical: *)
(* F outside 2, 3); ReducedContextIndex is the set c977wc_rindex of pairs    *)
(* (bp, v), v < LENGTH c977av_vectors.  WallCenterBarrier.center_above:     *)
(* WCB_CENTER_ABOVE.  Tag C977WC_.                                           *)
(* ========================================================================= *)

needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/AuxiliaryContext.ml";;
needs "n12/geometry/Anchors.ml";;

let c977wc_sq i =
  let w = Printf.sprintf "(c977av_ordered_owner c1 c2 a b l %d)" i in
  Printf.sprintf "(a %s) (b %s) (a %s * c1 %s + b %s * c2 %s - l / &2) (--b %s * c1 %s + a %s * c2 %s - l / &2) l"
    w w w w w w w w w w;;

let C977WC_HYP = "NPACK c1 c2 a b l /\\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family";;

let C977WC_TO_OO_TAC i =
  REWRITE_TAC[c977av_ordered_owner; C977AV_CODE_EL.(i)] THEN
  REWRITE_TAC[GSYM oou; GSYM oov] THEN REWRITE_TAC[GSYM ooc; GSYM oos];;

let C977WC_INST th = MP (SPEC_ALL (oo_inst `ccc977ri_family` th))
  (CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`));;

(* the pruned domain of slot i, split into its literal cases *)
let C977WC_DOMAIN_CASES_TAC i =
  MP_TAC(SPEC (mk_small_numeral i) (MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
           `b:num->real`; `l:real`] C977AV_PRUNED_AUXILIARY_DOMAIN_ACTUAL)
           (CONJ (ASSUME `NPACK c1 c2 a b l`)
                 (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`)))) THEN
  REWRITE_TAC[ARITH; C977AV_CODE_EL.(i)] THEN
  REWRITE_TAC[(REWRITE_CONV[c977av_prune4] THENC ONCE_DEPTH_CONV EL_CONV)
                (mk_comb(mk_comb(`EL:num->((num->bool)list)list->(num->bool)list`, mk_small_numeral i),
                 `c977av_prune4`)); MEM] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;;

(* Lean: left_auxiliary (private) *)
let C977WC_LEFT_AUXILIARY = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s ==> linside %s (&1) (&12 / &5) /\\ ~linside %s (&87 / &50) (&2)"
   C977WC_HYP (c977wc_sq 8) (c977wc_sq 8)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977WC_TO_OO_TAC 8 THEN
  REWRITE_TAC[oo_aux_point 11; oo_aux_point 13] THEN C977WC_DOMAIN_CASES_TAC 8);;

(* Lean: bottom_auxiliary (private) *)
let C977WC_BOTTOM_AUXILIARY = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s ==> linside %s (&12 / &5) (&1) /\\ ~linside %s (&2) (&87 / &50)"
   C977WC_HYP (c977wc_sq 9) (c977wc_sq 9)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977WC_TO_OO_TAC 9 THEN
  REWRITE_TAC[oo_aux_point 6; oo_aux_point 4] THEN C977WC_DOMAIN_CASES_TAC 9);;

(* facts of ordered owner i (unit normal, side, code) *)
let C977WC_FACTS_TAC i =
  let ow = mk_comb(`c977av_ordered_owner c1 c2 a b l`, mk_small_numeral i) in
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; ow] NPACK_SQ) THEN
  REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                mk_small_numeral i] C977AV_ORDERED_OWNER_CODE) THEN
  ASM_REWRITE_TAC[C977AV_CODE_EL.(i); ARITH] THEN DISCH_TAC;;

let C977WC_DISTINCT = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ~(c977av_ordered_owner c1 c2 a b l i = c977av_ordered_owner c1 c2 a b l j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977AV_ORDERED_OWNER_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[]);;

let C977WC_LDISJ_TAC i j =
  MATCH_MP_TAC NPACK_LDISJ THEN ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN
  MATCH_MP_TAC C977WC_DISTINCT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;;

(* Lean: left_center *)
let C977WC_LEFT_CENTER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> &2 < lcy %s" C977WC_HYP (c977wc_sq 8)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_LEFT_AUXILIARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977WC_FACTS_TAC 1 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 1`] C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN REWRITE_TAC[GSYM c977av_ordered_owner] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 8) (c977wc_sq 1))) MP_TAC THENL
   [C977WC_LDISJ_TAC 8 1; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&19 / &25`; `&187 / &100`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC WCB_CENTER_ABOVE THEN ASM_REWRITE_TAC[] THEN
  C977WC_FACTS_TAC 8 THEN ASM_REWRITE_TAC[] THEN
  C977WC_TO_OO_TAC 8 THEN ASM_SIMP_TAC[OO_BOX] THEN
  ACCEPT_TAC(C977WC_INST (oo_seed 4096 (`&457 / &500`, `&2`))));;

let C977WC_LCX_SW = prove
 (`forall c s u v a. lcx c s u v a = lcy s c u (--v - a) a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: bottom_center *)
let C977WC_BOTTOM_CENTER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> &2 < lcx %s" C977WC_HYP (c977wc_sq 9)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_BOTTOM_AUXILIARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977WC_FACTS_TAC 0 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_anchors] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 9) (c977wc_sq 0))) MP_TAC THENL
   [C977WC_LDISJ_TAC 9 0; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&187 / &100`; `&19 / &25`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 9 THEN
  ONCE_REWRITE_TAC[C977WC_LCX_SW] THEN
  MATCH_MP_TAC WCB_CENTER_ABOVE THEN ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCONT_PULLSW THEN C977WC_TO_OO_TAC 9 THEN ASM_SIMP_TAC[OO_BOX]; ALL_TAC] THEN
  C977WC_TO_OO_TAC 9 THEN
  ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`))));;

(* Lean: wall_branch_restriction *)
let C977WC_WALL_BRANCH_RESTRICTION = prove
 (`forall c1 c2 a b l w bb.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     c977wb_owners c1 c2 a b l w /\ c977wb_half c1 c2 a b l w bb
     ==> ~(bb 0) /\ ~(bb 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `w 0 = c977av_ordered_owner c1 c2 a b l 8 /\ w 1 = c977av_ordered_owner c1 c2 a b l 9`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OWNMASK_INJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
    ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN REWRITE_TAC[GSYM c977av_ordered_owner] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[c977wb_owners] o
      check (can (term_match [] `c977wb_owners c1 c2 a b l w`) o concl)) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    REWRITE_TAC[ARITH; C977WB_WALLCODE_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
      C977AV_ORDERED_OWNER_CODE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[ARITH] (SPEC `8` th);
                                                            REWRITE_RULE[ARITH] (SPEC `9` th)]) THEN
    REWRITE_TAC[C977AV_CODE_EL.(8); C977AV_CODE_EL.(9)];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_LEFT_CENTER) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_BOTTOM_CENTER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c977wb_half] o
    check (can (term_match [] `c977wb_half c1 c2 a b l w bb`) o concl)) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
  REWRITE_TAC[ARITH; c977wb_coord] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: OppositeWallBranch / expandWallBranch *)
let c977wc_expand = new_definition
 `c977wc_expand (bp:bool#bool) = \k:num. (k = 2 /\ FST bp) \/ (k = 3 /\ SND bp)`;;

(* Lean: expand_of_restriction (private) *)
let C977WC_EXPAND_OF_RESTRICTION = prove
 (`forall bb:num->bool. (forall k. ~(k < 4) ==> bb k = false) /\ ~(bb 0) /\ ~(bb 1)
     ==> c977wc_expand (bb 2, bb 3) = bb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; c977wc_expand] THEN X_GEN_TAC `k:num` THEN
  BETA_TAC THEN
  ASM_CASES_TAC `k < 4` THENL
   [UNDISCH_TAC `k < 4` THEN REWRITE_TAC[C977WB_LT4] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[ARITH];
    SUBGOAL_THEN `~(k = 2) /\ ~(k = 3)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(k < 4)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Lean: ReducedContextIndex *)
let c977wc_rindex = new_definition
 `c977wc_rindex = {(bp:bool#bool, v:num) | bp IN (:bool#bool) /\ v < LENGTH c977av_vectors}`;;

(* Lean: reduced_context_count *)
let C977WC_REDUCED_CONTEXT_COUNT = prove
 (`CARD c977wc_rindex = 228`,
  SUBGOAL_THEN `(:bool#bool) HAS_SIZE 4` ASSUME_TAC THENL
   [SUBGOAL_THEN `(:bool#bool) = {x,y | x IN (:bool) /\ y IN (:bool)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNIV; FORALL_PAIR_THM; IN_ELIM_PAIR_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(:bool)`; `2`; `(:bool)`; `2`] HAS_SIZE_PRODUCT) THEN
    REWRITE_TAC[HAS_SIZE_BOOL; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:bool#bool)`; `4`; `{v:num | v < LENGTH c977av_vectors}`; `LENGTH c977av_vectors`]
    HAS_SIZE_PRODUCT) THEN
  ASM_REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN
  SUBGOAL_THEN `{x,y | x IN (:bool#bool) /\ y IN {v:num | v < LENGTH c977av_vectors}} = c977wc_rindex`
    SUBST1_TAC THENL [REWRITE_TAC[c977wc_rindex; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[C977AV_AUXILIARY_VECTOR_COUNT] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[HAS_SIZE]);;

let C977WC_COVER_BODY =
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
      exists bp v. (bp,v) IN c977wc_rindex /\ c977wb_half d1 d2 e1 e2 l w (c977wc_expand bp) /\
             EL v c977av_vectors = c977av_actual d1 d2 e1 e2 l`;;

(* Lean: canonical_four_wall_context_cover *)
let C977WC_CANONICAL_FOUR_WALL_CONTEXT_COVER = prove
 (mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`, mk_forall(`b:num->real`,
  mk_forall(`l:real`, mk_imp(
   `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`,
   list_mk_exists([`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`], C977WC_COVER_BODY))))))),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977AC_CANONICAL_AUXILIARY_CONTEXT_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`((bb:num->bool) 2, bb 3)`; `v:num`] THEN
  UNDISCH_TAC `(bb:num->bool,v:num) IN c977ac_index` THEN
  REWRITE_TAC[c977ac_index; c977wc_rindex; IN_ELIM_PAIR_THM; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`;
                `w:num->num`; `bb:num->bool`] C977WC_WALL_BRANCH_RESTRICTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `bb:num->bool` C977WC_EXPAND_OF_RESTRICTION) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_of_four_wall_contexts *)
let C977WC_EXCLUDES_CASE_OF_FOUR_WALL_CONTEXTS = prove
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
      ==> forall w bp v. c977wb_owners c1 c2 a b l w /\ (bp,v) IN c977wc_rindex /\
                   c977wb_half c1 c2 a b l w (c977wc_expand bp) /\
                   EL v c977av_vectors = c977av_actual c1 c2 a b l ==> false)
   ==> excl_case 977`,
  DISCH_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977WC_CANONICAL_FOUR_WALL_CONTEXT_COVER) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`w:num->num`; `bp:bool#bool`; `v:num`]) THEN
  ASM_REWRITE_TAC[]);;
