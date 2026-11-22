(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner04.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain4 (C981ODM_DOMAIN4 of OwnershipDomains.ml) as the literal list      *)
(* c981cov_allowed4.  Lean's domain4.allowed is the list argument of the     *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO04_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed4 *)
let c981cov_allowed4 = new_definition
 `c981cov_allowed4:(num->bool)list =
   [{}; {11}; {1, 11}; {3}; {3, 11}; {3, 14}]`;;

(* Lean: allowed4_exact  (domain4.allowed = allowed4) *)
let C981CAO04_ALLOWED4_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN4), `c981cov_allowed4`),
  REWRITE_TAC[c981cov_allowed4; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain4 restated with the named list *)
let C981CAO04_DOMAIN4 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO04_ALLOWED4_EXACT)) C981ODM_DOMAIN4;;
