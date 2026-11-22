(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner07.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain7 (C981ODM_DOMAIN7 of OwnershipDomains.ml) as the literal list     *)
(* c981cov_allowed7.  Lean's domain7.allowed is the list argument of the    *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO07_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed7 *)
let c981cov_allowed7 = new_definition
 `c981cov_allowed7:(num->bool)list =
   [{1, 11}; {1, 13}; {1, 14}; {1, 11, 13}; {1, 11, 14}; {1, 13, 14}; {3, 11}; {3, 13}; {3, 14}; {3, 11, 13}; {3, 11, 14}; {3, 13, 14}; {5, 11}; {5, 13}; {5, 14}; {5, 11, 13}; {5, 11, 14}; {5, 13, 14}; {5, 13, 16}; {5, 13, 17}; {5, 14, 16}; {5, 14, 17}; {0, 1, 13}; {0, 1, 10, 13}; {0, 1, 11, 13}; {0, 1, 13, 14}; {0, 5, 13}; {0, 5, 13, 14}; {0, 5, 13, 16}; {0, 5, 13, 17}; {1, 3, 11}; {1, 3, 13}; {1, 3, 14}; {1, 3, 11, 13}; {1, 3, 11, 14}; {1, 3, 13, 14}; {1, 4, 13}; {1, 4, 11, 13}; {1, 4, 13, 14}; {1, 5, 11}; {1, 5, 13}; {1, 5, 14}; {1, 5, 11, 13}; {1, 5, 11, 14}; {1, 5, 13, 14}; {1, 5, 13, 16}; {1, 5, 13, 17}; {1, 5, 14, 16}; {1, 5, 14, 17}; {3, 5, 11}; {3, 5, 13}; {3, 5, 14}; {3, 5, 11, 13}; {3, 5, 11, 14}; {3, 5, 13, 14}; {3, 5, 13, 16}; {3, 5, 14, 16}; {3, 5, 14, 17}; {4, 5, 13}; {4, 5, 11, 13}; {4, 5, 13, 14}; {4, 5, 13, 16}; {4, 5, 13, 17}; {5, 7, 14, 17}]`;;

(* Lean: allowed7_exact  (domain7.allowed = allowed7) *)
let C981CAO07_ALLOWED7_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN7), `c981cov_allowed7`),
  REWRITE_TAC[c981cov_allowed7; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain7 restated with the named list *)
let C981CAO07_DOMAIN7 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO07_ALLOWED7_EXACT)) C981ODM_DOMAIN7;;
