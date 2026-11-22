(* ========================================================================= *)
(* Port of Compact/Completion/C981/OutwardTranspose.lean                     *)
(* (namespace N12Compact.C981CompletionOutwardTranspose).  The original row  *)
(* 55 enters the outward-anchor contradiction (C981OR_GEOMETRY) after        *)
(* transposing all actual owners: q i = transpose.pull (owners p (roles i)), *)
(* transpose = <true,false,false> is pullSwap (LINSIDE_PULLSW /              *)
(* LCONT_PULLSW), roles is the HOL list c981ot_roles (EL i).  Lean `Check v` *)
(* (transposed points in the computed query lists) and `excludes v checked`  *)
(* are the producer c981ot_excludes V (literal V): every point is built with *)
(* c981br_in / c981br_out (Bridge_C981Row27.ml) at the transposed point,     *)
(* which fail exactly when it is not in queryInsidePoints /                  *)
(* queryOutsidePoints.  Tag C981OT_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_OutwardRows.ml";;

(* Lean: transpose, roles *)
let c981ot_roles = new_definition
 `c981ot_roles = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10]`;;
let C981OT_ROLES = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10];;

(* Lean: injective (local of excludes), with the range of roles *)
let C981OT_ROLES_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ ~(i = j)
         ==> EL i c981ot_roles < 12 /\ EL j c981ot_roles < 12 /\
             ~(EL i c981ot_roles = EL j c981ot_roles)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981ot_roles] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* disjointness is preserved by pullSwap of both squares *)
let C981OT_LDISJ_PULLSW = prove
 (`forall c s u v a c' s' u' v' a'.
     ldisj s c u (--v - a) a s' c' u' (--v' - a') a' <=> ldisj c s u v a c' s' u' v' a'`,
  REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN MESON_TAC[]);;

(* Lean: Check, excludes *)
let c981ot_excludes vtm =
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let sw (x, y) = (y, x) in
  let pts prod l = List.concat (map (fun (i, ps) ->
      map (fun p -> MP (SPEC_ALL (prod vtm (el i C981OT_ROLES) (sw p))) h) ps) l) in
  let ins = pts c981br_in c981or_inside_list and outs = pts c981br_out c981or_outside_list in
  let f s = mk_abs(`i:num`, list_mk_comb(s, C981BR_VARS @ [`EL (EL i c981ot_roles) c981ow_masks`])) in
  let gth = SPECL [f `oos`; f `ooc`; f `oou`;
                   mk_abs(`i:num`, mk_binop `(-):real->real->real`
                     (mk_comb(`(--):real->real`, list_mk_comb(`oov`, C981BR_VARS @ [`EL (EL i c981ot_roles) c981ow_masks`])))
                     `l:real`);
                   mk_abs(`i:num`, `l:real`)] C981OR_GEOMETRY in
  let expand defs =
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC(defs @ [c981ow_masks; c981ot_roles]) THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[MEM; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM;
                FORALL_UNWIND_THM2; FST; SND; LINSIDE_PULLSW] in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC gth THEN BETA_TAC THEN
    REPEAT CONJ_TAC THEN
    FIRST [GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
           MATCH_MP_TAC OO_UNIT THEN ACCEPT_TAC np;
           GEN_TAC THEN DISCH_TAC THEN ACCEPT_TAC (MATCH_MP OO_SIDE np);
           GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LCONT_PULLSW THEN
           MATCH_MP_TAC OO_BOX THEN ACCEPT_TAC np;
           expand [c981or_insidePoints] THEN REWRITE_TAC ins THEN NO_TAC;
           expand [c981or_outsidePoints] THEN REWRITE_TAC outs THEN NO_TAC;
           REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[C981OT_LDISJ_PULLSW] THEN
           FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C981OT_ROLES_INJECTIVE) THEN
           MATCH_MP_TAC OO_LIST_APART THEN
           EXISTS_TAC `ccc981ri_family` THEN ASM_REWRITE_TAC[C981OW_LENGTH] THEN
           REWRITE_TAC[c981ow_masks] THEN REWRITE_TAC[fst C981OW_LIST; snd C981OW_LIST] THEN
           NO_TAC]);;

(* Lean: checked55, representative55_excluded *)
let C981OT_REPRESENTATIVE55_EXCLUDED = c981br_rep_excluded 55 c981ot_excludes;;
