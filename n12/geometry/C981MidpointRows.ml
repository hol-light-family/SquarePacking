(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981MidpointRows.lean                             *)
(* (namespace N12Compact.C981MidpointRows).  The original C981 packing entry *)
(* for the strengthened endpoint-row argument (EndpointRowTemplate.impossible*)
(* = ERT_IMPOSSIBLE applied to the pulled owners q i = d.transform.pull      *)
(* (owners p (d.roles i))).                                                  *)
(* As in C981TwoTipRows.ml: a Transform is an OCaml triple, Data the pair    *)
(* (transform, roles as a 4-tuple); c981mr_geom t is ERT_IMPOSSIBLE for the  *)
(* pulled squares, stated for the original squares at the transformed points*)
(* (the closed premises taken from strict ones, Lean `close`).  Data.Check   *)
(* quantifies over the computed query point lists, so `excludes d v checked` *)
(* is the producer c981mr_excludes d V (fails iff the check fails).          *)
(* ========================================================================= *)

needs "n12/geometry/EndpointRowTemplate.ml";;
needs "n12/geometry/C981.ml";;
needs "n12/geometry/C981TwoTipRows.ml";;

(* Lean: insidePoints, outsidePoints *)
let c981mr_inside_points = function
    0 -> [(`&2`, `&113 / &50`); (`&113 / &50`, `&2`); (`&47 / &20`, `&47 / &20`)]
  | 1 -> [(`&33 / &20`, `&47 / &20`); (`&87 / &50`, `&2`); (`&8 / &5`, `&3`)]
  | 2 -> [(`&1`, `&12 / &5`)]
  | _ -> [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`)];;
let c981mr_outside_points = function
    0 -> [(`&33 / &20`, `&33 / &20`); (`&47 / &20`, `&33 / &20`)]
  | 3 -> [(`&3`, `&87 / &50`)]
  | _ -> [];;

let C981MR_SQ = map (fun n -> map (fun f -> mk_var(f ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"])
                    ["A"; "B"; "L"; "R"];;

(* Lean: close (private): LINSIDE_CLOSED *)

(* EndpointRowTemplate.impossible for the pulled squares *)
let c981mr_geom t =
  let sq i = el i C981MR_SQ in
  let unit i = let [c; s; _; _; a] = sq i in
               [mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                        (mk_binop `( * ):real->real->real` s s), `&1`);
                mk_binop `(<):real->real->bool` `&0` a] in
  let side i = mk_binop `(<):real->real->bool` `&1` (last (sq i)) in
  let ins i = map (fun p -> c981ttr_lin (sq i) (c981ttr_apply t p)) (c981mr_inside_points i)
  and outs i = map (fun p -> mk_neg (c981ttr_lin (sq i) (c981ttr_apply t p))) (c981mr_outside_points i) in
  let disj i j = list_mk_comb(`ldisj`, sq i @ sq j) in
  let hyps = List.concat (map unit [0; 1; 2; 3]) @ map side [0; 1; 3] @
             [list_mk_comb(`lcont`, sq 3)] @
             List.concat (map (fun i -> ins i @ outs i) [0; 1; 2; 3]) @
             [disj 0 1; disj 0 3; disj 1 2] in
  let goal = list_mk_forall(List.concat C981MR_SQ, mk_imp(list_mk_conj hyps, `false`)) in
  let gth = SPECL (List.concat (map (c981ttr_pull t) C981MR_SQ)) ERT_IMPOSSIBLE in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC gth THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    REWRITE_TAC[lsquare; LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW;
                LCLOSED_PULLX; LCLOSED_PULLY; LCLOSED_PULLSW; ldisj] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[LINSIDE_CLOSED; LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: Data, Data.Check, excludes *)
let c981mr_excludes (t, (r0, r1, r2, r3)) v =
  let rs = [r0; r1; r2; r3] in
  if length (setify rs) < 4 then failwith "c981mr_excludes: roles not injective" else
  let ins i = map (fun p -> c981br_in v (el i rs) (c981ttr_apply t p)) (c981mr_inside_points i)
  and outs i = map (fun p -> c981br_out v (el i rs) (c981ttr_apply t p)) (c981mr_outside_points i) in
  c981br_prove_excl v (c981mr_geom t) rs
    (List.concat (map (fun i -> ins i @ outs i) [0; 1; 2; 3]) @
     [c981br_apart v r0 r1; c981br_apart v r0 r3; c981br_apart v r1 r2]);;

(* Lean: northEast, northWest *)
let c981mr_north_east = ((false, false, false), (6, 7, 8, 10));;
let c981mr_north_west = ((false, true, false), (7, 6, 10, 8));;

(* Lean: northEastIds, northWestIds, coveredIds *)
let C981MR_NE = [75; 78; 82; 84; 85; 88; 92; 96; 97; 100; 102];;
let C981MR_NW = [9; 10; 11; 12; 13; 14; 17; 18; 45; 46; 47; 49; 67; 68; 72];;
let c981mr_north_east_ids = new_definition
 `c981mr_north_east_ids = [75; 78; 82; 84; 85; 88; 92; 96; 97; 100; 102]`;;
let c981mr_north_west_ids = new_definition
 `c981mr_north_west_ids = [9; 10; 11; 12; 13; 14; 17; 18; 45; 46; 47; 49; 67; 68; 72]`;;
let c981mr_covered_ids = new_definition
 `c981mr_covered_ids = APPEND c981mr_north_east_ids c981mr_north_west_ids`;;

(* Lean: northEast_checked, northWest_checked (with excludes applied) *)
let C981MR_NORTH_EAST_CHECKED = map (fun i -> c981br_rep_excluded i (c981mr_excludes c981mr_north_east)) C981MR_NE;;
let C981MR_NORTH_WEST_CHECKED = map (fun i -> c981br_rep_excluded i (c981mr_excludes c981mr_north_west)) C981MR_NW;;

(* Lean: covered_excluded *)
let C981MR_COVERED_EXCLUDED =
  let th = c981br_covered (C981MR_NE @ C981MR_NW) (C981MR_NORTH_EAST_CHECKED @ C981MR_NORTH_WEST_CHECKED) in
  prove(`forall i. MEM i c981mr_covered_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
        REWRITE_TAC[c981mr_covered_ids; c981mr_north_east_ids; c981mr_north_west_ids; APPEND] THEN
        ACCEPT_TAC th);;

(* Lean: newlyResidualIds, pendingResidualIds *)
let c981mr_newly_residual_ids = new_definition
 `c981mr_newly_residual_ids = [45; 46; 47; 49; 67; 68; 72; 75; 78; 96]`;;
let c981mr_pending_residual_ids = new_definition
 `c981mr_pending_residual_ids = FILTER (\i. ~MEM i c981mr_covered_ids) c981c_remaining_indices`;;

let C981MR_COVERED_LIT = prove
 (`c981mr_covered_ids = [75; 78; 82; 84; 85; 88; 92; 96; 97; 100; 102;
                         9; 10; 11; 12; 13; 14; 17; 18; 45; 46; 47; 49; 67; 68; 72]`,
  REWRITE_TAC[c981mr_covered_ids; c981mr_north_east_ids; c981mr_north_west_ids; APPEND]);;

(* evaluation of FILTER over literal num lists, one element at a time *)
let C981MR_FILTER_CONV =
  let dec = BETA_CONV THENC REWRITE_CONV[MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] in
  let ct, cf = CONJUNCT1 (SPEC_ALL COND_CLAUSES), CONJUNCT2 (SPEC_ALL COND_CLAUSES) in
  let rec filt tm =
    (REWR_CONV (CONJUNCT1 FILTER) ORELSEC
     (REWR_CONV (CONJUNCT2 FILTER) THENC RATOR_CONV (RATOR_CONV (RAND_CONV dec)) THENC
      ((REWR_CONV ct THENC RAND_CONV filt) ORELSEC (REWR_CONV cf THENC filt)))) tm in
  REWRITE_CONV[C981MR_COVERED_LIT; c981c_remaining_indices] THENC filt;;

(* Lean: covered_count *)
let C981MR_COVERED_COUNT = prove
 (`LENGTH c981mr_covered_ids = 26`,
  REWRITE_TAC[C981MR_COVERED_LIT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: residual_difference *)
let C981MR_RESIDUAL_DIFFERENCE = prove
 (`FILTER (\i. MEM i c981mr_covered_ids) c981c_remaining_indices = c981mr_newly_residual_ids`,
  CONV_TAC(LAND_CONV C981MR_FILTER_CONV) THEN REWRITE_TAC[c981mr_newly_residual_ids]);;

(* Lean: pending_residual_count *)
let C981MR_PENDING_RESIDUAL_COUNT = prove
 (`LENGTH c981mr_pending_residual_ids = 45`,
  REWRITE_TAC[c981mr_pending_residual_ids] THEN CONV_TAC(LAND_CONV(RAND_CONV C981MR_FILTER_CONV)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
