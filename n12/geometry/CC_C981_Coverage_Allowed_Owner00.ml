(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner00.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain0 (C981ODM_DOMAIN0 of OwnershipDomains.ml) as the literal list      *)
(* c981cov_allowed0.  Lean's domain0.allowed is the list argument of the     *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO00_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed0 *)
let c981cov_allowed0 = new_definition
 `c981cov_allowed0:(num->bool)list =
   [{2, 12}; {2, 10, 12}]`;;

(* Lean: allowed0_exact  (domain0.allowed = allowed0) *)
let C981CAO00_ALLOWED0_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN0), `c981cov_allowed0`),
  REWRITE_TAC[c981cov_allowed0; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain0 restated with the named list *)
let C981CAO00_DOMAIN0 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO00_ALLOWED0_EXACT)) C981ODM_DOMAIN0;;
