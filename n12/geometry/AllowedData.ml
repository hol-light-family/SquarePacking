(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/AllowedData.lean                    *)
(* (S12Completion.C981.Coverage).  The twelve literal allowed lists of the    *)
(* C981 owner domains, and their reordering.  Lean's                          *)
(* domains.map (fun d => d.allowed) is the HOL list of the list arguments of  *)
(* the domain theorems C981ODM_DOMAINS (the list enumerated by                *)
(* c981odm_assignments); reorder is cro_reorder (CoverageReorder.ml).         *)
(* Tag C981AD_.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;
needs "n12/geometry/CoverageReorder.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner00.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner01.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner02.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner03.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner04.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner05.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner06.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner07.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner08.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner09.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner10.ml";;
needs "n12/geometry/CC_C981_Coverage_Allowed_Owner11.ml";;

(* Lean: literalChoices *)
let c981cov_literal_choices = new_definition
 `c981cov_literal_choices:((num->bool)list)list =
   [c981cov_allowed0; c981cov_allowed1; c981cov_allowed2; c981cov_allowed3;
    c981cov_allowed4; c981cov_allowed5; c981cov_allowed6; c981cov_allowed7;
    c981cov_allowed8; c981cov_allowed9; c981cov_allowed10; c981cov_allowed11]`;;

let C981AD_EXACTS =
  [C981CAO00_ALLOWED0_EXACT; C981CAO01_ALLOWED1_EXACT; C981CAO02_ALLOWED2_EXACT;
   C981CAO03_ALLOWED3_EXACT; C981CAO04_ALLOWED4_EXACT; C981CAO05_ALLOWED5_EXACT;
   C981CAO06_ALLOWED6_EXACT; C981CAO07_ALLOWED7_EXACT; C981CAO08_ALLOWED8_EXACT;
   C981CAO09_ALLOWED9_EXACT; C981CAO10_ALLOWED10_EXACT; C981CAO11_ALLOWED11_EXACT];;

(* Lean: allowed_exact  (domains.map (fun d => d.allowed) = literalChoices) *)
let C981AD_ALLOWED_EXACT =
  let ty = `:(num->bool)list` in
  let cons = mk_const("CONS", [ty, aty]) in
  let rec go ths = match ths with
      [] -> REFL (mk_const("NIL", [ty, aty]))
    | th :: t -> MK_COMB(AP_TERM cons th, go t) in
  let lhs_ok th d = lhs(concl th) = rand(concl d) in
  if not (forall2 lhs_ok C981AD_EXACTS C981ODM_DOMAINS) then
    failwith "C981AD_ALLOWED_EXACT: domains" else
  TRANS (go C981AD_EXACTS) (SYM c981cov_literal_choices);;

(* Lean: reorderedChoices *)
let c981cov_reordered_choices = new_definition
 `c981cov_reordered_choices:((num->bool)list)list =
   [c981cov_allowed0; c981cov_allowed1; c981cov_allowed8; c981cov_allowed9;
    c981cov_allowed10; c981cov_allowed11; c981cov_allowed2; c981cov_allowed3;
    c981cov_allowed4; c981cov_allowed5; c981cov_allowed6; c981cov_allowed7]`;;

(* Lean: reordered_exact *)
let C981AD_REORDERED_EXACT = prove
 (`cro_reorder c981cov_literal_choices = c981cov_reordered_choices`,
  REWRITE_TAC[cro_reorder; c981cov_literal_choices; c981cov_reordered_choices] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[cro_take; cro_drop; APPEND] THEN
                     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV))) THEN
  REWRITE_TAC[]);;
