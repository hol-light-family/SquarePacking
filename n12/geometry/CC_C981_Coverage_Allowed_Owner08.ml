(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner08.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain8 (C981ODM_DOMAIN8 of OwnershipDomains.ml) as the literal list     *)
(* c981cov_allowed8.  Lean's domain8.allowed is the list argument of the    *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO08_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed8 *)
let c981cov_allowed8 = new_definition
 `c981cov_allowed8:(num->bool)list =
   [{0, 10}; {0, 10, 13}; {1, 11}; {1, 11, 13}; {0, 1, 10}; {0, 1, 11}; {0, 1, 10, 11}; {0, 1, 10, 13}; {0, 1, 11, 13}; {0, 2, 10}; {1, 3, 11}]`;;

(* Lean: allowed8_exact  (domain8.allowed = allowed8) *)
let C981CAO08_ALLOWED8_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN8), `c981cov_allowed8`),
  REWRITE_TAC[c981cov_allowed8; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain8 restated with the named list *)
let C981CAO08_DOMAIN8 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO08_ALLOWED8_EXACT)) C981ODM_DOMAIN8;;
