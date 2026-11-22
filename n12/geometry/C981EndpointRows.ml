(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981EndpointRows.lean                             *)
(* (namespace N12Compact.C981EndpointRows).  Two perpendicular spans close   *)
(* the cases in which the right wall owns the lower point                    *)
(* (EndpointRowTemplate.dual_impossible = ERT_DUAL_IMPOSSIBLE at the owners  *)
(* roles = [6,7,5,8,9]).  As in C981MidpointRows.ml, Check quantifies over   *)
(* the computed query point lists, so `excludes v checked` is the producer   *)
(* c981er_excludes V (fails iff the check fails); C981ER_GEOM is             *)
(* dual_impossible with the closed premises taken from strict ones (Lean     *)
(* `close`).                                                                 *)
(* ========================================================================= *)

needs "n12/geometry/C981MidpointRows.ml";;

(* Lean: roles, insidePoints, outsidePoints *)
let C981ER_ROLES = [6; 7; 5; 8; 9];;
let c981er_inside_points = function
    0 -> [(`&2`, `&113 / &50`); (`&113 / &50`, `&2`); (`&47 / &20`, `&47 / &20`)]
  | 1 -> [(`&87 / &50`, `&2`); (`&8 / &5`, `&3`)]
  | 2 -> [(`&2`, `&87 / &50`); (`&3`, `&8 / &5`)]
  | 3 -> [(`&1`, `&12 / &5`)]
  | _ -> [(`&12 / &5`, `&1`)];;
let c981er_outside_points =
  [(`&33 / &20`, `&33 / &20`); (`&47 / &20`, `&33 / &20`); (`&33 / &20`, `&47 / &20`);
   (`&3`, `&12 / &5`); (`&12 / &5`, `&3`)];;

(* Lean: close (private) + dual_impossible *)
let C981ER_GEOM = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cC sC uC vC aC cL sL uL vL aL cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aA /\ &1 < aB /\ &1 < aC /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     linside cB sB uB vB aB (&87 / &50) (&2) /\
     linside cB sB uB vB aB (&8 / &5) (&3) /\
     linside cC sC uC vC aC (&2) (&87 / &50) /\
     linside cC sC uC vC aC (&3) (&8 / &5) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     linside cD sD uD vD aD (&12 / &5) (&1) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cC sC uC vC aC /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cC sC uC vC aC cD sD uD vD aD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ERT_DUAL_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
    `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN
  ASM_SIMP_TAC[lsquare; LINSIDE_CLOSED]);;

(* Lean: Check, excludes *)
let c981er_excludes v =
  let rs = C981ER_ROLES in
  let ins i = map (fun p -> c981br_in v (el i rs) p) (c981er_inside_points i) in
  c981br_prove_excl v C981ER_GEOM rs
    (List.concat (map ins [0; 1; 2; 3; 4]) @
     map (fun p -> c981br_out v 6 p) c981er_outside_points @
     [c981br_apart v 6 7; c981br_apart v 6 5; c981br_apart v 7 8; c981br_apart v 5 9]);;

(* Lean: additionalIds, coveredIds *)
let c981er_additional_ids = new_definition `c981er_additional_ids = [76; 77; 83]`;;
let c981er_covered_ids = new_definition
 `c981er_covered_ids = APPEND c981mr_covered_ids c981er_additional_ids`;;

(* Lean: additional_checked (with excludes applied) *)
let C981ER_ADDITIONAL_CHECKED = map (fun i -> c981br_rep_excluded i c981er_excludes) [76; 77; 83];;

(* Lean: covered_excluded *)
let C981ER_COVERED_EXCLUDED = prove
 (`forall i. MEM i c981er_covered_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  REWRITE_TAC[c981er_covered_ids; MEM_APPEND] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[C981MR_COVERED_EXCLUDED];
    MP_TAC(REWRITE_RULE[GSYM c981er_additional_ids]
             (c981br_covered [76; 77; 83] C981ER_ADDITIONAL_CHECKED)) THEN
    ASM_MESON_TAC[]]);;

(* Lean: newlyResidualIds, pendingResidualIds *)
let c981er_newly_residual_ids = new_definition
 `c981er_newly_residual_ids = [45; 46; 47; 49; 67; 68; 72; 75; 76; 77; 78; 96]`;;
let c981er_pending_residual_ids = new_definition
 `c981er_pending_residual_ids = FILTER (\i. ~MEM i c981er_covered_ids) c981c_remaining_indices`;;

let C981ER_COVERED_LIT = prove
 (`c981er_covered_ids = [75; 78; 82; 84; 85; 88; 92; 96; 97; 100; 102;
                         9; 10; 11; 12; 13; 14; 17; 18; 45; 46; 47; 49; 67; 68; 72; 76; 77; 83]`,
  REWRITE_TAC[c981er_covered_ids; C981MR_COVERED_LIT; c981er_additional_ids; APPEND]);;

(* evaluation of FILTER over literal num lists, one element at a time *)
let C981ER_FILTER_CONV =
  let dec = BETA_CONV THENC REWRITE_CONV[MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] in
  let ct, cf = CONJUNCT1 (SPEC_ALL COND_CLAUSES), CONJUNCT2 (SPEC_ALL COND_CLAUSES) in
  let rec filt tm =
    (REWR_CONV (CONJUNCT1 FILTER) ORELSEC
     (REWR_CONV (CONJUNCT2 FILTER) THENC RATOR_CONV (RATOR_CONV (RAND_CONV dec)) THENC
      ((REWR_CONV ct THENC RAND_CONV filt) ORELSEC (REWR_CONV cf THENC filt)))) tm in
  REWRITE_CONV[C981ER_COVERED_LIT; c981c_remaining_indices] THENC filt;;

(* Lean: covered_count *)
let C981ER_COVERED_COUNT = prove
 (`LENGTH c981er_covered_ids = 29`,
  REWRITE_TAC[C981ER_COVERED_LIT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: residual_difference *)
let C981ER_RESIDUAL_DIFFERENCE = prove
 (`FILTER (\i. MEM i c981er_covered_ids) c981c_remaining_indices = c981er_newly_residual_ids`,
  CONV_TAC(LAND_CONV C981ER_FILTER_CONV) THEN REWRITE_TAC[c981er_newly_residual_ids]);;

(* Lean: pending_residual_count *)
let C981ER_PENDING_RESIDUAL_COUNT = prove
 (`LENGTH c981er_pending_residual_ids = 43`,
  REWRITE_TAC[c981er_pending_residual_ids] THEN CONV_TAC(LAND_CONV(RAND_CONV C981ER_FILTER_CONV)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
