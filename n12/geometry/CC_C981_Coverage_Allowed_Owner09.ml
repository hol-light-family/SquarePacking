(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner09.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain9 (C981ODM_DOMAIN9 of OwnershipDomains.ml) as the literal list     *)
(* c981cov_allowed9.  Lean's domain9.allowed is the list argument of the    *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO09_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed9 *)
let c981cov_allowed9 = new_definition
 `c981cov_allowed9:(num->bool)list =
   [{2, 12}; {2, 10, 12}; {2, 12, 15}; {6, 15}; {6, 12, 15}; {6, 15, 18}; {2, 4, 12}; {2, 4, 12, 15}; {2, 6, 12, 15}; {4, 6, 15}; {4, 6, 12, 15}]`;;

(* Lean: allowed9_exact  (domain9.allowed = allowed9) *)
let C981CAO09_ALLOWED9_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN9), `c981cov_allowed9`),
  REWRITE_TAC[c981cov_allowed9; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain9 restated with the named list *)
let C981CAO09_DOMAIN9 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO09_ALLOWED9_EXACT)) C981ODM_DOMAIN9;;
