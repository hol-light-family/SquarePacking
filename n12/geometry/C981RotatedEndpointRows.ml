(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981RotatedEndpointRows.lean                      *)
(* (namespace N12Compact.C981RotatedEndpointRows).  Coordinate exchange      *)
(* exposes the same complete endpoint ending at the other two available      *)
(* central markers.  C981MidpointRows.Data is the OCaml pair                 *)
(* (transform, roles) of C981MidpointRows.ml; `Data.Check v` is decided by    *)
(* the producer c981mr_excludes d V (fails iff the check fails), which also *)
(* gives `C981MidpointRows.excludes d v checked`.  Tag C981RER_.             *)
(* ========================================================================= *)

needs "n12/geometry/C981EndpointRows.ml";;

(* Lean: east, southEast *)
let c981rer_east = ((true, false, false), (6, 5, 9, 11));;
let c981rer_south_east = ((true, false, true), (5, 6, 11, 9));;

(* Lean: eastIds, southEastIds *)
let C981RER_EAST = [75; 76; 79; 80; 81; 82; 83; 84; 86; 87; 88; 89; 90; 91; 92; 102];;
let C981RER_SOUTH_EAST = [15; 16; 48; 61; 62; 63; 64; 65; 74];;
let c981rer_east_ids = new_definition
 `c981rer_east_ids = [75; 76; 79; 80; 81; 82; 83; 84; 86; 87; 88; 89; 90; 91; 92; 102]`;;
let c981rer_south_east_ids = new_definition
 `c981rer_south_east_ids = [15; 16; 48; 61; 62; 63; 64; 65; 74]`;;

(* Lean: east_checked, southEast_checked (with C981MidpointRows.excludes applied) *)
let C981RER_EAST_CHECKED =
  map (fun i -> c981br_rep_excluded i (c981mr_excludes c981rer_east)) C981RER_EAST;;
let C981RER_SOUTH_EAST_CHECKED =
  map (fun i -> c981br_rep_excluded i (c981mr_excludes c981rer_south_east)) C981RER_SOUTH_EAST;;

(* Lean: additionalIds, coveredIds *)
let c981rer_additional_ids = new_definition
 `c981rer_additional_ids =
    FILTER (\i. ~MEM i c981er_covered_ids) (APPEND c981rer_east_ids c981rer_south_east_ids)`;;
let c981rer_covered_ids = new_definition
 `c981rer_covered_ids = APPEND c981er_covered_ids c981rer_additional_ids`;;

(* evaluation of FILTER over literal num lists, one element at a time *)
let C981RER_FILTER_CONV =
  let dec = BETA_CONV THENC REWRITE_CONV[MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] in
  let ct, cf = CONJUNCT1 (SPEC_ALL COND_CLAUSES), CONJUNCT2 (SPEC_ALL COND_CLAUSES) in
  let rec filt tm =
    (REWR_CONV (CONJUNCT1 FILTER) ORELSEC
     (REWR_CONV (CONJUNCT2 FILTER) THENC RATOR_CONV (RATOR_CONV (RAND_CONV dec)) THENC
      ((REWR_CONV ct THENC RAND_CONV filt) ORELSEC (REWR_CONV cf THENC filt)))) tm in
  filt;;

(* Lean: additional_literal *)
let C981RER_ADDITIONAL_LITERAL = prove
 (`c981rer_additional_ids =
     [79; 80; 81; 86; 87; 89; 90; 91; 15; 16; 48; 61; 62; 63; 64; 65; 74]`,
  REWRITE_TAC[c981rer_additional_ids; C981ER_COVERED_LIT; c981rer_east_ids; c981rer_south_east_ids;
              APPEND] THEN
  CONV_TAC(LAND_CONV C981RER_FILTER_CONV) THEN REFL_TAC);;

let C981RER_COVERED_LIT =
  REWRITE_RULE[C981ER_COVERED_LIT; C981RER_ADDITIONAL_LITERAL; APPEND] c981rer_covered_ids;;

(* Lean: covered_excluded *)
let C981RER_COVERED_EXCLUDED = prove
 (`forall i. MEM i c981rer_covered_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  REWRITE_TAC[c981rer_covered_ids; MEM_APPEND] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[C981ER_COVERED_EXCLUDED];
    (* every added id is in eastIds ++ southEastIds *)
    MP_TAC(c981br_covered (C981RER_EAST @ C981RER_SOUTH_EAST)
             (C981RER_EAST_CHECKED @ C981RER_SOUTH_EAST_CHECKED)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `MEM (i:num) c981rer_additional_ids` THEN
    REWRITE_TAC[C981RER_ADDITIONAL_LITERAL; MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: newlyResidualIds, pendingResidualIds *)
let c981rer_newly_residual_ids = new_definition
 `c981rer_newly_residual_ids = [45; 46; 47; 49; 67; 68; 72; 75; 76; 77; 78; 79; 96]`;;
let c981rer_pending_residual_ids = new_definition
 `c981rer_pending_residual_ids = FILTER (\i. ~MEM i c981rer_covered_ids) c981c_remaining_indices`;;

let C981RER_REMAINING_FILTER_CONV =
  REWRITE_CONV[C981RER_COVERED_LIT; c981c_remaining_indices] THENC C981RER_FILTER_CONV;;

(* Lean: covered_count *)
let C981RER_COVERED_COUNT = prove
 (`LENGTH c981rer_covered_ids = 46`,
  REWRITE_TAC[C981RER_COVERED_LIT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: residual_difference *)
let C981RER_RESIDUAL_DIFFERENCE = prove
 (`FILTER (\i. MEM i c981rer_covered_ids) c981c_remaining_indices = c981rer_newly_residual_ids`,
  CONV_TAC(LAND_CONV C981RER_REMAINING_FILTER_CONV) THEN REWRITE_TAC[c981rer_newly_residual_ids]);;

(* Lean: pending_residual_count *)
let C981RER_PENDING_RESIDUAL_COUNT = prove
 (`LENGTH c981rer_pending_residual_ids = 42`,
  REWRITE_TAC[c981rer_pending_residual_ids] THEN
  CONV_TAC(LAND_CONV(RAND_CONV C981RER_REMAINING_FILTER_CONV)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
