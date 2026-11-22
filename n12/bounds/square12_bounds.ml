(* ========================================================================= *)
(* Bounds for s(12).                                                         *)
(* ========================================================================= *)

needs "n12/bounds/cert_check.ml";;
needs "n12/upper.ml";;

let SIDE_BOUNDS_FROM = prove
 (`forall n m u. (forall t. t < m ==> ~packs n t) /\ packs n u
           ==> m <= square_packing_side n /\ square_packing_side n <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[square_packing_side] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INF THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[REAL_NOT_LT]];
    MATCH_MP_TAC INF_LE_ELEMENT THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:real` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_NOT_LT]]);;
