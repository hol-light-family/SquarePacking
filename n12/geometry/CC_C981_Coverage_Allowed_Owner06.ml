(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner06.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain6 (C981ODM_DOMAIN6 of OwnershipDomains.ml) as the literal list     *)
(* c981cov_allowed6.  Lean's domain6.allowed is the list argument of the    *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO06_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed6 *)
let c981cov_allowed6 = new_definition
 `c981cov_allowed6:(num->bool)list =
   [{5, 16}; {5, 13, 16}; {5, 14, 16}; {5, 17}; {5, 13, 17}; {5, 14, 17}; {5, 16, 17}; {5, 19}; {5, 16, 19}; {5, 17, 19}; {3, 5, 14, 17}; {4, 5, 16}; {4, 5, 13, 16}; {4, 5, 14, 16}; {4, 5, 16, 17}; {4, 5, 16, 19}; {7, 16}; {7, 17}; {7, 16, 17}; {7, 19}; {7, 16, 19}; {7, 17, 19}; {5, 7, 16}; {5, 7, 13, 16}; {5, 7, 17}; {5, 7, 13, 17}; {5, 7, 14, 17}; {5, 7, 16, 17}; {5, 7, 19}; {5, 7, 16, 19}; {5, 7, 17, 19}; {5, 8, 16}; {5, 8, 13, 16}; {5, 8, 14, 16}; {5, 8, 16, 17}; {9, 16}; {9, 17}; {9, 16, 17}; {9, 19}; {9, 16, 19}; {9, 17, 19}; {4, 9, 16}; {4, 9, 16, 17}; {4, 9, 16, 19}; {5, 9, 16}; {5, 9, 13, 16}; {5, 9, 14, 16}; {5, 9, 17}; {5, 9, 13, 17}; {5, 9, 14, 17}; {5, 9, 16, 17}; {5, 9, 19}; {5, 9, 16, 19}; {5, 9, 17, 19}; {7, 9, 16}; {7, 9, 17}; {7, 9, 16, 17}; {7, 9, 19}; {7, 9, 16, 19}; {7, 9, 17, 19}; {8, 9, 16}; {8, 9, 16, 17}; {8, 9, 16, 18}; {8, 9, 16, 19}]`;;

(* Lean: allowed6_exact  (domain6.allowed = allowed6) *)
let C981CAO06_ALLOWED6_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN6), `c981cov_allowed6`),
  REWRITE_TAC[c981cov_allowed6; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain6 restated with the named list *)
let C981CAO06_DOMAIN6 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO06_ALLOWED6_EXACT)) C981ODM_DOMAIN6;;
