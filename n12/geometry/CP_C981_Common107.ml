(* ========================================================================= *)
(* Port of Compact/Completion/C981/Common107.lean                             *)
(* (N12Compact.C981CompletionCommon107).  The original row 107 enters the   *)
(* common-cycle contradiction (C981CR_GEOMETRY) after transposing the whole  *)
(* packing: q i = transpose.pull (owners p (roles i)), transpose =           *)
(* <true,false,false> is pullSwap (tuple s, c, u, --v - a, a; LINSIDE_PULLSW *)
(* / LCONT_PULLSW / C981OT_LDISJ_PULLSW), roles = c981c107_roles.  Lean      *)
(* `Check v` and `excludes v checked` are the producer c981c107_excludes V   *)
(* (literal V): every point comes from c981br_in / c981br_out at the         *)
(* transposed point (they fail exactly when it is not in queryInsidePoints / *)
(* queryOutsidePoints), the center from c981dwe_center V 0                   *)
(* (DoubleWallElbows.center, placement 0, owner 5 at (2,2), fails unless     *)
(* PlacementCheck v 0), disjointness from c981br_apart (distinct masks, i.e. *)
(* injectivity of roles on the used pairs).  Tag C981C107_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_CommonRows.ml";;
needs "n12/geometry/CP_C981_OutwardTranspose.ml";;
needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: transpose, roles *)
let c981c107_roles = new_definition
 `c981c107_roles = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10]`;;
let C981C107_ROLES = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10];;

(* Lean: injective (local of excludes) *)
let C981C107_ROLES_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ ~(i = j) ==> ~(EL i c981c107_roles = EL j c981c107_roles)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981c107_roles] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* the pulled owner tuple of q i *)
let c981c107_q i =
  match c981br_owner (el i C981C107_ROLES) with
    [c; s; u; v; a] ->
      [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c981c107_q";;

(* Lean: Check, excludes *)
let c981c107_excludes vtm =
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let tup i = c981br_owner (el i C981C107_ROLES) in
  let swiff i (x, y) = SYM (SPECL (tup i @ [x; y]) LINSIDE_PULLSW) in
  let pin i (x, y) =
    EQ_MP (swiff i (x, y)) (MP (SPEC_ALL (c981br_in vtm (el i C981C107_ROLES) (y, x))) h) in
  let pout i (x, y) =
    EQ_MP (AP_TERM `(~)` (swiff i (x, y)))
      (MP (SPEC_ALL (c981br_out vtm (el i C981C107_ROLES) (y, x))) h) in
  let ins = List.concat (map (fun (i, ps) -> map (pin i) ps) c981cr_inside) in
  let outpts = List.concat (map (fun (i, ps) -> map (pout i) ps) c981cr_outside) in
  let center =
    let c0 = MP (SPEC_ALL (c981dwe_center vtm 0)) h in
    EQ_MP (swiff 7 (`&2`, `&2`)) c0 in
  let apart (i, j) =
    let d = MP (SPEC_ALL (c981br_apart vtm (el i C981C107_ROLES) (el j C981C107_ROLES))) h in
    EQ_MP (SYM (SPECL (tup i @ tup j) C981OT_LDISJ_PULLSW)) d in
  let aps = map apart [8, 1; 8, 7; 11, 6; 11, 7; 4, 8; 4, 11; 7, 6; 6, 10; 6, 3] in
  let side = MATCH_MP OO_SIDE np in
  let per i =
    let mt = mk_small_numeral (c981br_mask (el i C981C107_ROLES)) in
    [ONCE_REWRITE_RULE[REAL_ADD_SYM] (SPEC mt (MATCH_MP OO_UNIT np));
     MATCH_MP LCONT_PULLSW (SPEC mt (MATCH_MP OO_BOX np))] in
  let owners = [1; 3; 4; 6; 7; 8; 10; 11] in
  let gth = SPECL (List.concat (map c981c107_q owners)) C981CR_GEOMETRY in
  let ths = side :: ins @ outpts @ [center] @ aps @ List.concat (map per owners) in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC gth THEN REWRITE_TAC ths);;

(* Lean: checked, representative107_excluded *)
let C981C107_REPRESENTATIVE107_EXCLUDED = c981br_rep_excluded 107 c981c107_excludes;;
