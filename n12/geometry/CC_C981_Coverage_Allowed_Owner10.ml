(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner10.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain10 (C981ODM_DOMAIN10 of OwnershipDomains.ml) as the literal list     *)
(* c981cov_allowed10.  Lean's domain10.allowed is the list argument of the    *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO10_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed10 *)
let c981cov_allowed10 = new_definition
 `c981cov_allowed10:(num->bool)list =
   [{8, 18}; {8, 16, 18}; {9, 19}; {9, 16, 19}; {6, 8, 18}; {7, 9, 19}; {8, 9, 18}; {8, 9, 19}; {8, 9, 16, 18}; {8, 9, 16, 19}; {8, 9, 18, 19}]`;;

(* Lean: allowed10_exact  (domain10.allowed = allowed10) *)
let C981CAO10_ALLOWED10_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN10), `c981cov_allowed10`),
  REWRITE_TAC[c981cov_allowed10; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain10 restated with the named list *)
let C981CAO10_DOMAIN10 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO10_ALLOWED10_EXACT)) C981ODM_DOMAIN10;;
