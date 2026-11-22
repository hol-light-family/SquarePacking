(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner05.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain5 (C981ODM_DOMAIN5 of OwnershipDomains.ml) as the literal list      *)
(* c981cov_allowed5.  Lean's domain5.allowed is the list argument of the     *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO05_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;
needs "n12/geometry/Allowed05.ml";;

(* Lean: allowed5_exact  (domain5.allowed = allowed5) *)
let C981CAO05_ALLOWED5_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN5), `c981cov_allowed5`),
  REWRITE_TAC[c981cov_allowed5; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain5 restated with the named list *)
let C981CAO05_DOMAIN5 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO05_ALLOWED5_EXACT)) C981ODM_DOMAIN5;;
