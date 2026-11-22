(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner03.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain3 (C981ODM_DOMAIN3 of OwnershipDomains.ml) as the literal list      *)
(* c981cov_allowed3.  Lean's domain3.allowed is the list argument of the     *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO03_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed3 *)
let c981cov_allowed3 = new_definition
 `c981cov_allowed3:(num->bool)list =
   [{}; {19}; {7}; {7, 17}; {7, 19}; {9, 19}]`;;

(* Lean: allowed3_exact  (domain3.allowed = allowed3) *)
let C981CAO03_ALLOWED3_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN3), `c981cov_allowed3`),
  REWRITE_TAC[c981cov_allowed3; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain3 restated with the named list *)
let C981CAO03_DOMAIN3 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO03_ALLOWED3_EXACT)) C981ODM_DOMAIN3;;
