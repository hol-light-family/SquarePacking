(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner11.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain11 (C981ODM_DOMAIN11 of OwnershipDomains.ml) as the literal list     *)
(* c981cov_allowed11.  Lean's domain11.allowed is the list argument of the    *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO11_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed11 *)
let c981cov_allowed11 = new_definition
 `c981cov_allowed11:(num->bool)list =
   [{3, 14}; {3, 11, 14}; {3, 14, 17}; {7, 17}; {7, 14, 17}; {7, 17, 19}; {3, 5, 14}; {3, 5, 14, 17}; {3, 7, 14, 17}; {5, 7, 17}; {5, 7, 14, 17}]`;;

(* Lean: allowed11_exact  (domain11.allowed = allowed11) *)
let C981CAO11_ALLOWED11_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN11), `c981cov_allowed11`),
  REWRITE_TAC[c981cov_allowed11; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain11 restated with the named list *)
let C981CAO11_DOMAIN11 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO11_ALLOWED11_EXACT)) C981ODM_DOMAIN11;;
