(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/DomainCache.lean.                  *)
(* Lean cache / cacheNamed are cdom_cache / dc_cache_named (the mask is the *)
(* theorem's, "same" is checked).                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_DomainTransport.ml";;

(* Lean: filter_subset_of_indexed *)
let DC_FILTER_SUBSET_OF_INDEXED = prove
 (`forall (input:A list) output keep count. LENGTH input = count /\
     (forall i. i < count /\ keep (EL i input) ==> MEM (EL i input) output)
     ==> forall v. MEM v (FILTER keep input) ==> MEM v output`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[MEM_FILTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[MEM_EXISTS_EL])) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* Lean: cache *)
let dc_cache th mask al =
  if cdom_mask th <> mask then failwith "dc_cache: mask" else cdom_cache th al;;

(* Lean: cacheNamed *)
let dc_cache_named (th, inth) mask al = (dc_cache th mask al, inth);;
