(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner01.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain1 (C981ODM_DOMAIN1 of OwnershipDomains.ml) as the literal list      *)
(* c981cov_allowed1.  Lean's domain1.allowed is the list argument of the     *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO01_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed1 *)
let c981cov_allowed1 = new_definition
 `c981cov_allowed1:(num->bool)list =
   [{0, 10}; {0, 2, 10}]`;;

(* Lean: allowed1_exact  (domain1.allowed = allowed1) *)
let C981CAO01_ALLOWED1_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN1), `c981cov_allowed1`),
  REWRITE_TAC[c981cov_allowed1; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain1 restated with the named list *)
let C981CAO01_DOMAIN1 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO01_ALLOWED1_EXACT)) C981ODM_DOMAIN1;;
