(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981TwoTipRows.lean                               *)
(* (namespace N12Compact.C981TwoTipRows).  Eleven whole original C981        *)
(* representative-vector exclusions; each placement moves the two actual     *)
(* owners together (C981TwoTip.impossible = C981TT_IMPOSSIBLE applied to the *)
(* pulled owners d.transform.pull (owners p (d.roles i))).                   *)
(* A Transform <swap,reflectX,reflectY> is an OCaml triple; Data is the      *)
(* pair (transform, (roles 0, roles 1)).  Transform.pull is                  *)
(* pullSwap o pullY o pullX on the 5-tuple (p2_base LINSIDE_PULLX/Y/SW), so  *)
(* inside_pull / rat_inside_transform become rewriting with LINSIDE_PULL*;   *)
(* c981ttr_geom t is C981TT_IMPOSSIBLE for the pulled squares, stated for    *)
(* the original squares at the transformed points t.applyRat P.              *)
(* Data.Check quantifies over the computed query point lists; `excludes d v  *)
(* checked` is the producer c981ttr_excludes d V (fails iff the check fails: *)
(* roles not injective, or a point not in queryInside/OutsidePoints).        *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/C981TwoTip.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: insidePoints, outsidePoints *)
let c981ttr_inside_points = function
    0 -> [(`&47 / &20`, `&47 / &20`); (`&12 / &5`, `&3`)]
  | _ -> [(`&113 / &50`, `&2`); (`&3`, `&12 / &5`)];;
let c981ttr_outside_points = function
    0 -> [(`&87 / &50`, `&3`)]
  | _ -> [(`&3`, `&87 / &50`)];;

(* Lean: Transform.applyRat (rational literals) *)
let c981ttr_apply (sw, rx, ry) (x, y) =
  let red t = rand (concl (REAL_RAT_REDUCE_CONV t)) in
  let sub4 t = red (mk_binop `(-):real->real->real` `&4` t) in
  let (u, v) = if sw then (y, x) else (x, y) in
  ((if rx then sub4 u else u), (if ry then sub4 v else v));;

(* Lean: Transform.pull on a 5-tuple of terms *)
let c981ttr_pull (sw, rx, ry) [c; s; u; v; a] =
  let pullx [c; s; u; v; a] =
    [mk_comb(`(--):real->real`, c); s; mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` c);
     mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a)
       (mk_binop `( * ):real->real->real` `&4` s); a]
  and pully [c; s; u; v; a] =
    [c; mk_comb(`(--):real->real`, s); mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` s);
     mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_binop `( * ):real->real->real` `&4` c) v) a; a]
  and pullsw [c; s; u; v; a] =
    [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a] in
  let q1 = if rx then pullx [c; s; u; v; a] else [c; s; u; v; a] in
  let q2 = if ry then pully q1 else q1 in
  if sw then pullsw q2 else q2;;

let C981TTR_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let C981TTR_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

let c981ttr_lin q (x, y) = list_mk_comb(`linside`, q @ [x; y]);;

(* C981TwoTip.impossible for the pulled squares q i = t.pull (A / B) *)
let c981ttr_geom t =
  let ins q i = map (fun p -> c981ttr_lin q (c981ttr_apply t p)) (c981ttr_inside_points i)
  and outs q i = map (fun p -> mk_neg (c981ttr_lin q (c981ttr_apply t p))) (c981ttr_outside_points i) in
  let hyps =
    [`cA * cA + sA * sA = &1`; `&0 < aA`; `cB * cB + sB * sB = &1`; `&0 < aB`; `&1 < aA`; `&1 < aB`] @
    ins C981TTR_A 0 @ outs C981TTR_A 0 @ ins C981TTR_B 1 @ outs C981TTR_B 1 @
    [list_mk_comb(`ldisj`, C981TTR_A @ C981TTR_B)] in
  let goal = list_mk_forall(C981TTR_A @ C981TTR_B, mk_imp(list_mk_conj hyps, `false`)) in
  let gth = SPECL (c981ttr_pull t C981TTR_A @ c981ttr_pull t C981TTR_B) C981TT_IMPOSSIBLE in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC gth THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; ldisj] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: Data, Data.Check, excludes *)
let c981ttr_excludes (t, (r0, r1)) v =
  if r0 = r1 then failwith "c981ttr_excludes: roles not injective" else
  let ins r i = map (fun p -> c981br_in v r (c981ttr_apply t p)) (c981ttr_inside_points i)
  and outs r i = map (fun p -> c981br_out v r (c981ttr_apply t p)) (c981ttr_outside_points i) in
  c981br_prove_excl v (c981ttr_geom t) [r0; r1]
    (ins r0 0 @ outs r0 0 @ ins r1 1 @ outs r1 1 @ [c981br_apart v r0 r1]);;

(* Lean: northEast, northWest, southEast *)
let c981ttr_north_east = ((false, false, false), (6, 10));;
let c981ttr_north_west = ((false, true, false), (7, 8));;
let c981ttr_south_east = ((true, false, true), (5, 9));;

(* Lean: northEastIds, northWestIds, southEastIds, coveredIds *)
let c981ttr_north_east_ids = new_definition `c981ttr_north_east_ids = [25; 31; 40; 70]`;;
let c981ttr_north_west_ids = new_definition `c981ttr_north_west_ids = [32; 33; 38; 57; 99]`;;
let c981ttr_south_east_ids = new_definition `c981ttr_south_east_ids = [94; 95]`;;
let c981ttr_covered_ids = new_definition
 `c981ttr_covered_ids = APPEND (APPEND c981ttr_north_east_ids c981ttr_north_west_ids) c981ttr_south_east_ids`;;

(* Lean: northEast_checked, northWest_checked, southEast_checked
   (with excludes applied: the per-row vector exclusions) *)
let C981TTR_NORTH_EAST_CHECKED = map (fun i -> c981br_rep_excluded i (c981ttr_excludes c981ttr_north_east)) [25; 31; 40; 70];;
let C981TTR_NORTH_WEST_CHECKED = map (fun i -> c981br_rep_excluded i (c981ttr_excludes c981ttr_north_west)) [32; 33; 38; 57; 99];;
let C981TTR_SOUTH_EAST_CHECKED = map (fun i -> c981br_rep_excluded i (c981ttr_excludes c981ttr_south_east)) [94; 95];;

(* Lean: covered_excluded *)
let C981TTR_COVERED_EXCLUDED =
  let th = c981br_covered [25; 31; 40; 70; 32; 33; 38; 57; 99; 94; 95]
             (C981TTR_NORTH_EAST_CHECKED @ C981TTR_NORTH_WEST_CHECKED @ C981TTR_SOUTH_EAST_CHECKED) in
  prove(`forall i. MEM i c981ttr_covered_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
        REWRITE_TAC[c981ttr_covered_ids; c981ttr_north_east_ids; c981ttr_north_west_ids;
                    c981ttr_south_east_ids; APPEND] THEN ACCEPT_TAC th);;

(* Lean: covered_count *)
let C981TTR_COVERED_COUNT = prove
 (`LENGTH c981ttr_covered_ids = 11`,
  REWRITE_TAC[c981ttr_covered_ids; c981ttr_north_east_ids; c981ttr_north_west_ids;
              c981ttr_south_east_ids; APPEND; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
