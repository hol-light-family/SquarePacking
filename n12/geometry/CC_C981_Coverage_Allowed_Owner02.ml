(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Allowed/Owner02.lean               *)
(* (S12Completion.C981.Coverage).  The allowed list of the C981 owner domain  *)
(* domain2 (C981ODM_DOMAIN2 of OwnershipDomains.ml) as the literal list      *)
(* c981cov_allowed2.  Lean's domain2.allowed is the list argument of the     *)
(* domain theorem |- cdom ccc981ri_family m al.  Tag C981CAO02_.             *)
(* ========================================================================= *)

needs "n12/geometry/OwnershipDomains.ml";;

(* Lean: allowed2 *)
let c981cov_allowed2 = new_definition
 `c981cov_allowed2:(num->bool)list =
   [{}; {18}; {6}; {6, 15}; {6, 18}; {8, 18}]`;;

(* Lean: allowed2_exact  (domain2.allowed = allowed2) *)
let C981CAO02_ALLOWED2_EXACT = prove
 (mk_eq(rand(concl C981ODM_DOMAIN2), `c981cov_allowed2`),
  REWRITE_TAC[c981cov_allowed2; CONS_11] THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(setlit_eq (lhs w) (rhs w))));;

(* domain2 restated with the named list *)
let C981CAO02_DOMAIN2 =
  CONV_RULE (RAND_CONV (REWR_CONV C981CAO02_ALLOWED2_EXACT)) C981ODM_DOMAIN2;;
