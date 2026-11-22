(* ========================================================================= *)
(* Port of Compact/Completion/C981/Last104.lean                               *)
(* (N12Compact.C981CompletionLast104).  The original row 104 enters the     *)
(* final-cycle contradiction of LastRows (C981LR_GEOMETRY) after transposing *)
(* the whole packing: q i = transpose.pull (owners p (roles i)), transpose = *)
(* <true,false,false> is pullSwap (tuple s, c, u, --v - a, a; LINSIDE_PULLSW *)
(* / LCONT_PULLSW / C981OT_LDISJ_PULLSW), roles = c981l104_roles.  Lean      *)
(* `Check v` and `excludes v checked` are the producer c981l104_excludes V   *)
(* (literal V): every point comes from c981br_in / c981br_out at the         *)
(* transposed point (they fail exactly when it is not in queryInsidePoints / *)
(* queryOutsidePoints), the center from c981dwe_center V 0                   *)
(* (DoubleWallElbows.center, placement 0, owner 5 at (2,2), fails unless     *)
(* PlacementCheck v 0), disjointness from c981br_apart (distinct masks, i.e. *)
(* injectivity of roles on the used pairs), cap from OO_SIDE_LE.             *)
(* Same structure as CP_C981_Common107.ml.  Tag C981L104_.                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_LastRows.ml";;
needs "n12/geometry/CP_C981_OutwardTranspose.ml";;
needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: transpose, roles *)
let c981l104_roles = new_definition
 `c981l104_roles = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10]`;;
let C981L104_ROLES = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10];;

(* Lean: injective (local of excludes) *)
let C981L104_ROLES_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ ~(i = j) ==> ~(EL i c981l104_roles = EL j c981l104_roles)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981l104_roles] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* the pulled owner tuple of q i *)
let c981l104_q i =
  match c981br_owner (el i C981L104_ROLES) with
    [c; s; u; v; a] ->
      [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c981l104_q";;

(* Lean: Check, excludes *)
let c981l104_excludes vtm =
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let tup i = c981br_owner (el i C981L104_ROLES) in
  let swiff i (x, y) = SYM (SPECL (tup i @ [x; y]) LINSIDE_PULLSW) in
  let pin i (x, y) =
    EQ_MP (swiff i (x, y)) (MP (SPEC_ALL (c981br_in vtm (el i C981L104_ROLES) (y, x))) h) in
  let pout i (x, y) =
    EQ_MP (AP_TERM `(~)` (swiff i (x, y)))
      (MP (SPEC_ALL (c981br_out vtm (el i C981L104_ROLES) (y, x))) h) in
  let ins = List.concat (map (fun (i, ps) -> map (pin i) ps) c981lr_inside) in
  let outpts = List.concat (map (fun (i, ps) -> map (pout i) ps) c981lr_outside) in
  let center =
    let c0 = MP (SPEC_ALL (c981dwe_center vtm 0)) h in
    EQ_MP (swiff 7 (`&2`, `&2`)) c0 in
  let apart (i, j) =
    let d = MP (SPEC_ALL (c981br_apart vtm (el i C981L104_ROLES) (el j C981L104_ROLES))) h in
    EQ_MP (SYM (SPECL (tup i @ tup j) C981OT_LDISJ_PULLSW)) d in
  let aps = map apart C981LR_APART in
  let side = MATCH_MP OO_SIDE np in
  let cap = MATCH_MP OO_SIDE_LE np in
  let per i =
    let mt = mk_small_numeral (c981br_mask (el i C981L104_ROLES)) in
    [ONCE_REWRITE_RULE[REAL_ADD_SYM] (SPEC mt (MATCH_MP OO_UNIT np));
     MATCH_MP LCONT_PULLSW (SPEC mt (MATCH_MP OO_BOX np))] in
  let owners = C981LR_OWNERS in
  let gth = SPECL (List.concat (map c981l104_q owners)) C981LR_GEOMETRY in
  let ths = side :: cap :: ins @ outpts @ [center] @ aps @ List.concat (map per owners) in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC gth THEN REWRITE_TAC ths);;

(* Lean: checked, representative104_excluded *)
let C981L104_REPRESENTATIVE104_EXCLUDED = c981br_rep_excluded 104 c981l104_excludes;;
