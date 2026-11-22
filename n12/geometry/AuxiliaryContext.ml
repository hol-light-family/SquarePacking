(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/AuxiliaryContext.lean.                     *)
(* Conventions of Context.ml / AuxiliaryVectors.ml / WallBranches.ml.        *)
(* A ContextIndex = WallBranch x Fin auxiliaryVectors.length is a pair       *)
(* (bb, v) with bb : num->bool canonical (bb k = F for k >= 4, see           *)
(* WallBranches.ml) and v < LENGTH c977av_vectors; the set of all of them    *)
(* is c977ac_index.  auxiliaryVectors.get v is EL v c977av_vectors;          *)
(* orderedOwner q 0 is c977av_ordered_owner d1 d2 e1 e2 l 0;                 *)
(* actualAuxiliaryVector q is c977av_actual d1 d2 e1 e2 l.  Tag C977AC_.     *)
(* ========================================================================= *)

needs "n12/geometry/Context.ml";;
needs "n12/geometry/AuxiliaryVectors.ml";;

(* Lean: ContextIndex *)
let c977ac_index = new_definition
 `c977ac_index = {(bb:num->bool, v:num) | (forall k. ~(k < 4) ==> bb k = false) /\ v < LENGTH c977av_vectors}`;;

(* Lean: context_count *)
let C977AC_CONTEXT_COUNT = prove
 (`CARD c977ac_index = 912`,
  MP_TAC(ISPECL [`false`; `2`; `(:bool)`; `4`; `{k:num | k < 4}`] HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_LT; HAS_SIZE_BOOL; IN_UNIV; IN_ELIM_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{bb:num->bool | forall k. ~(k < 4) ==> bb k = false}`; `16`;
                 `{v:num | v < LENGTH c977av_vectors}`; `LENGTH c977av_vectors`] HAS_SIZE_PRODUCT) THEN
  ASM_REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN
  SUBGOAL_THEN `{x,y | x IN {bb:num->bool | forall k. ~(k < 4) ==> ~(bb k)} /\
                       y IN {v:num | v < LENGTH c977av_vectors}} = c977ac_index` SUBST1_TAC THENL
   [REWRITE_TAC[c977ac_index; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[C977AV_AUXILIARY_VECTOR_COUNT] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[HAS_SIZE]);;

(* Lean: ordered_missing_corner_owner *)
let C977AC_ORDERED_MISSING_CORNER_OWNER = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1
     ==> c977av_ordered_owner c1 c2 a b l 0 = i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OWNMASK_INJ THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `0`]
    C977AV_ORDERED_OWNER_CODE) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[c977av_code; EL; HD]);;

let C977AC_COVER_BODY =
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
      exists bb v. (bb,v) IN c977ac_index /\ c977wb_half d1 d2 e1 e2 l w bb /\
             EL v c977av_vectors = c977av_actual d1 d2 e1 e2 l`;;

(* Lean: canonical_auxiliary_context_cover *)
let C977AC_CANONICAL_AUXILIARY_CONTEXT_COVER = prove
 (mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`, mk_forall(`b:num->real`,
  mk_forall(`l:real`, mk_imp(
   `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`,
   list_mk_exists([`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`], C977AC_COVER_BODY))))))),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977CTX_CANONICAL_BOUNDED_WALL_CONTEXT_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`; `i:num`]
    C977AC_ORDERED_MISSING_CORNER_OWNER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]
    C977AV_ACTUAL_AUXILIARY_VECTOR_MEM) THEN
  ASM_REWRITE_TAC[MEM_EXISTS_EL] THEN DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`\k:num. k < 4 /\ bb k`; `v:num`] THEN
  ASM_REWRITE_TAC[c977ac_index; IN_ELIM_PAIR_THM] THEN (CONJ_TAC THENL
   [MESON_TAC[];
    UNDISCH_TAC `c977wb_half d1 d2 e1 e2 l w bb` THEN
    REWRITE_TAC[c977wb_half] THEN MESON_TAC[]]));;

(* Lean: retained_canonical_auxiliary_context_cover *)
let C977AC_RETAINED_CANONICAL_AUXILIARY_CONTEXT_COVER = prove
 (mk_forall(`r:num`, mk_imp(`r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977`,
  mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`, mk_forall(`b:num->real`,
  mk_forall(`l:real`, mk_imp(
   `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)`,
   list_mk_exists([`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`], C977AC_COVER_BODY))))))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C977AC_CANONICAL_AUXILIARY_CONTEXT_COVER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_of_auxiliary_contexts *)
let C977AC_EXCLUDES_CASE_OF_AUXILIARY_CONTEXTS = prove
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
      ==> forall w bb v. c977wb_owners c1 c2 a b l w /\ (bb,v) IN c977ac_index /\
                   c977wb_half c1 c2 a b l w bb /\
                   EL v c977av_vectors = c977av_actual c1 c2 a b l ==> false)
   ==> excl_case 977`,
  DISCH_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977AC_CANONICAL_AUXILIARY_CONTEXT_COVER) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`w:num->num`; `bb:num->bool`; `v:num`]) THEN
  ASM_REWRITE_TAC[]);;
