(* ========================================================================= *)
(* Port of Compact/Cases/C868/Complete.lean (N12Compact.C868).               *)
(* Complete original-owner C868 assembly: every canonical frame of owner     *)
(* 3072 has negative sine (NonnegativeSector), and the negative sign is      *)
(* impossible by UpperNegativeCap.impossible (C868CG_IMPOSSIBLE) on          *)
(* N = H.translated 2 2 against the positive frame T of owner 32768          *)
(* translated by (2,2) (ClosedFrames.positive_frame = CLF_POSITIVE_FRAME).   *)
(* Lean H.translated 2 2 = (cH, sH, uH - (cH * &2 + sH * &2),                *)
(* vH - (--sH * &2 + cH * &2), aH), inside_translated_iff =                  *)
(* C868UI_INSIDE_TRANSLATED.  Lean UpperNegativeCap.Data N = c868cg_data N.  *)
(* family_excluded / row_lookup / row_family / case_excluded via RowIdentity *)
(* (row 455).  Tag C868C_.                                                   *)
(* ========================================================================= *)

needs "n12/geometry/NonnegativeSector.ml";;
needs "n12/geometry/UpperNegativeCapGeometry.ml";;
needs "n12/geometry/ActualTopBar.ml";;
needs "n12/geometry/RowIdentity.ml";;

let C868C_TR = [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`; `vH - (--sH * &2 + cH * &2)`; `aH:real`];;

let C868C_TR32768 =
  let [c; s; u; v; a] = c868_own 32768 in
  let m x y = mk_binop `(*):real->real->real` x y and p x y = mk_binop `(+):real->real->real` x y
  and d x y = mk_binop `(-):real->real->real` x y in
  [c; s; d u (p (m c `&2`) (m s `&2`)); d v (p (m (mk_comb(`(--):real->real`, s)) `&2`) (m c `&2`)); a];;

(* top_bar with the bar hypotheses as an implication (fact under C868_H) *)
let C868C_TOP_BAR_IMP =
  GENL C868OW_VARS (DISCH C868_H (GEN `x:real` (DISCH `&6 / &5 <= x /\ x <= &87 / &50`
    (MP (SPECL (C868OW_VARS @ [`x:real`]) C868TB_TOP_BAR)
        (CONJ C868_NP (CONJ (CONJUNCT2 (ASSUME C868_H)) (ASSUME `&6 / &5 <= x /\ x <= &87 / &50`)))))));;

(* Lean: negative_upper_frames_impossible *)
let C868C_NEGATIVE_UPPER_FRAMES_IMPOSSIBLE = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> false`,
  C868UI_INTRO_TAC THEN
  C868UI_APP_TAC C868UI_NEGATIVE_UPPER_INPUT THEN
  C868UI_APP_TAC C868NR_NEGATIVE_UPPER_NEAR_LOWER THEN
  C868UI_APP_TAC C868OE_NEGATIVE_UPPER_TOP_CAP THEN
  C868UI_APP_TAC C868CF_NEGATIVE_UPPER_SOUTHEAST_CAPS THEN
  (* Lean: input *)
  SUBGOAL_THEN (list_mk_comb(`c868cg_data`, C868C_TR)) ASSUME_TAC THENL
   [REWRITE_TAC[c868cg_data] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASSUME_TAC C868_SIDE THEN ASSUME_TAC C868_POS THEN
  (* T: ClosedFrames.positive_frame of owner 32768 translated by (2,2) *)
  MP_TAC (SPECL C868C_TR32768 CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ACCEPT_TAC (c868_unit 32768); ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`] THEN STRIP_TAC THEN
  MP_TAC (SPECL (C868C_TR @ [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`]) C868CG_IMPOSSIBLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ldisj] THEN C868UI_IFF_TAC THEN REWRITE_TAC[C868UI_INSIDE_TRANSLATED] THEN
  C868UI_IFF_TAC THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  (* far, marker, disjoint *)
  ASSUME_TAC (MP (SPECL [`&6 / &5`] (c868_mp C868C_TOP_BAR_IMP)) (REAL_ARITH `&6 / &5 <= &6 / &5 /\ &6 / &5 <= &87 / &50`)) THEN
  ASSUME_TAC (c868_seed_f 32768 (`&2`, `&1543 / &500`)) THEN
  ASSUME_TAC (REWRITE_RULE[ldisj] (c868_apart_f 3072 32768)) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: family_impossible *)
let C868C_FAMILY_IMPOSSIBLE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP OO_SIDE) THEN
  MP_TAC (SPECL (c868_own 3072) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C868PS_SQ_H THEN STRIP_TAC THEN
  MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_H) C868NS_UPPER_NEGATIVE_REQUIRED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_H) C868C_NEGATIVE_UPPER_FRAMES_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: family_excluded *)
let C868C_FAMILY_EXCLUDED = prove
 (`excl_fam c868_family`,
  REWRITE_TAC[excl_fam] THEN MESON_TAC[C868C_FAMILY_IMPOSSIBLE]);;

(* Lean: row_lookup (private), row_family, case_excluded *)
let C868C_ROW_LOOKUP = ri_lookup 455 `c868_family`;;
let C868C_ROW_FAMILY = ri_family_at 455 `c868_family`;;
let C868C_CASE_EXCLUDED = prove
 (`excl_case 868`,
  REWRITE_TAC[ri_excludes_case_iff 455 `c868_family`] THEN ACCEPT_TAC C868C_FAMILY_EXCLUDED);;

(* for the assembly: |- EXCLUDED_ROW 455 *)
let C868C_EXCLUDED_ROW = ri_excluded_row 455 C868C_CASE_EXCLUDED;;
