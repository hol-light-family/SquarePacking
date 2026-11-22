(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C997Points.lean.                  *)
(* An acyclic compulsory-point chain for the original C997 packing.         *)
(* The private lemma  absent  (auxiliary_disjoint) is applied inside        *)
(* OO_CHAIN_TAC (OO_EXCLUDE_ALL_TAC); the C997FiniteCuts list checks are    *)
(* re-evaluated there by OO_DOMAIN_CASES_TAC on the same C997 domains.      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C997FiniteCuts.ml";;

let C997PT_DOMS = [1, C997D_SOUTHWEST; 8192, C997D_BOTTOM; 256, C997D_SOUTHWEST_CENTRAL;
                   32768, C997D_TOP; 512, C997D_SOUTHEAST; 16384, C997D_RIGHT; 1024, C997D_NORTHEAST];;

(* Lean: absent (private) *)
let C997PT_ABSENT = prove
 (`forall c1 c2 a b l m n index. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family /\
     m IN c997e_family /\ n IN c997e_family /\ ~(m = n) /\ index IN ooaux c1 c2 a b l n
     ==> ~(index IN ooaux c1 c2 a b l m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `c997e_family`; `m:num`; `n:num`] OO_AUX_DISJOINT) THEN
  ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;

(* Lean: compulsory *)
let C997PT_COMPULSORY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family
     ==> (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
         (7 IN ooaux c1 c2 a b l 32768 /\ 17 IN ooaux c1 c2 a b l 32768) /\
         (8 IN ooaux c1 c2 a b l 512 /\ 18 IN ooaux c1 c2 a b l 512) /\
         (9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384) /\
         (5 IN ooaux c1 c2 a b l 1024 /\ 16 IN ooaux c1 c2 a b l 1024)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 IN ooaux c1 c2 a b l 2` ASSUME_TAC THENL
   [OO_SEED_MEM_TAC C997E_F 2 0 [(`&1`, `&87 / &50`)]; ALL_TAC] THEN
  SUBGOAL_THEN `3 IN ooaux c1 c2 a b l 2240` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM (oo_aux_point 3)] THEN
    ASM_SIMP_TAC[C997E_MERGED_OUTWARD]; ALL_TAC] THEN
  OO_CHAIN_TAC C997E_F C997PT_DOMS
   [1, [2]; 8192, [6; 15]; 256, [4]; 32768, [7; 17]; 512, [8]; 16384, [9; 19]; 1024, [5; 16]; 512, [18]]);;

(* Lean: auxiliary_inside *)
let C997PT_AUXILIARY_INSIDE = prove
 (`forall c1 c2 a b l mask index. NPACK c1 c2 a b l /\ index < 20 /\ index IN ooaux c1 c2 a b l mask
     ==> linside (ooc c1 c2 a b l mask) (oos c1 c2 a b l mask) (oou c1 c2 a b l mask)
                 (oov c1 c2 a b l mask) l (EL index (AUXPTS 2)$1) (EL index (AUXPTS 2)$2)`,
  MESON_TAC[OO_AUX_EXACT]);;
