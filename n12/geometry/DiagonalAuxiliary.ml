(* ========================================================================= *)
(* Phase 2: Completion/Cases/C981/DiagonalAuxiliary.lean.                    *)
(* Conventions of CornerReduction.ml and CC_C981_Ownership.ml:               *)
(* diagonal.pullPacking p of (c1,c2,a,b,l) is the packing (c2,c1,b,a,l);     *)
(* natCombinedOwners p i is auxown 2 (c1 i) (c2 i) (a i) (b i) l and         *)
(* natCombinedOwners p (ownerIndex p m) is ooaux c1 c2 a b l m;              *)
(* AuxExact q 2 S is !j. j < 20 ==> (linside q (EL j (AUXPTS 2)$1)           *)
(* (EL j (AUXPTS 2)$2) <=> j IN S);  (auxPoints 2)[k]! is EL k (AUXPTS 2);   *)
(* Fin 20 -> Fin 20 auxiliaryTranspose i is EL i c981da_aux_tr (i < 20),     *)
(* ownerTranspose i is EL i c981da_owner_tr (i < 12), ownerMasks i is        *)
(* EL i c981ow_masks;  Finset.range 20 is {j | j < 20};  candidateMasks is   *)
(* CANDMASKS.  The square pullSwap q of q = (c,s,u,v,a) is s c u (--v - a) a.*)
(* Tag C981DA_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CornerReduction.ml";;
needs "n12/geometry/CC_C981_Ownership.ml";;

(* Lean: auxiliaryTranspose *)
let c981da_aux_tr = new_definition
 `c981da_aux_tr = [12; 15; 10; 18; 13; 16; 11; 19; 14; 17; 2; 6; 0; 4; 8; 1; 5; 9; 3; 7]`;;

let C981DA_AUX_TR_LT = prove
 (`forall i. i < 20 ==> EL i c981da_aux_tr < 20`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981da_aux_tr] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: auxiliaryTranspose_point  (the point of the transposed index is the
   coordinate swap of the point: both coordinates) *)
let C981DA_AUXILIARYTRANSPOSE_POINT = prove
 (`forall i. i < 20
       ==> EL (EL i c981da_aux_tr) (AUXPTS 2)$1 = EL i (AUXPTS 2)$2 /\
           EL (EL i c981da_aux_tr) (AUXPTS 2)$2 = EL i (AUXPTS 2)$1`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981da_aux_tr; AUXPTS_EXPL.(2)] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[VECTOR_2]);;

(* Lean: auxiliaryTranspose_pattern *)
let C981DA_AUXILIARYTRANSPOSE_PATTERN = prove
 (`forall i. i < 20 ==> (EL i c981da_aux_tr IN {4, 6, 15} <=> i IN {1, 11, 13})`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981da_aux_tr; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: auxiliary_transpose_exact *)
let C981DA_AUXILIARY_TRANSPOSE_EXACT = prove
 (`forall c s u v a.
     (forall j. j < 20 ==> (linside c s u v a (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=> j IN {4, 6, 15}))
     ==> (forall j. j < 20 ==> (linside s c u (--v - a) a (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
                          j IN {1, 11, 13}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LINSIDE_PULLSW] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL j c981da_aux_tr`) THEN
  ASM_SIMP_TAC[C981DA_AUX_TR_LT; C981DA_AUXILIARYTRANSPOSE_POINT;
               C981DA_AUXILIARYTRANSPOSE_PATTERN]);;

(* Lean: nat_combined_subset20 *)
let C981DA_NAT_COMBINED_SUBSET20 = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12
     ==> auxown 2 (c1 i) (c2 i) (a i) (b i) l SUBSET {j | j < 20}`,
  REWRITE_TAC[auxown; SUBSET; IN_ELIM_THM; LEN_AUX.(2)] THEN MESON_TAC[]);;

let C981DA_AUXOWN_SUBSET20 = prove
 (`forall c1 c2 a b l. auxown 2 c1 c2 a b l SUBSET {j | j < 20}`,
  REWRITE_TAC[auxown; SUBSET; IN_ELIM_THM; LEN_AUX.(2)] THEN MESON_TAC[]);;

(* Lean: nat_combined_eq_of_exact *)
let C981DA_NAT_COMBINED_EQ_OF_EXACT = prove
 (`forall c1 c2 a b l i sown. NPACK c1 c2 a b l /\ i < 12 /\ sown SUBSET {j | j < 20} /\
     (forall j. j < 20 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                              (--b i * c1 i + a i * c2 i - l / &2) l
                              (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=> j IN sown))
     ==> auxown 2 (c1 i) (c2 i) (a i) (b i) l = sown`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j < 20` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[PK_COMBINED_EXACT];
    MP_TAC(SPECL [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`; `(b:num->real) i`;
                  `l:real`] C981DA_AUXOWN_SUBSET20) THEN
    UNDISCH_TAC `sown SUBSET {j | j < 20}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* Lean: ownerTranspose *)
let c981da_owner_tr = new_definition
 `c981da_owner_tr = [1; 0; 4; 3; 2; 7; 6; 5; 9; 8; 11; 10]`;;

let C981DA_OWNER_TR_LT = prove
 (`forall i. i < 12 ==> EL i c981da_owner_tr < 12`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981da_owner_tr] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let C981DA_DIAG_MASKS = map c981cr_diag_mask C981OW_MASKS;;

(* Lean: ownerMasks_transpose *)
let C981DA_OWNERMASKS_TRANSPOSE = prove
 (`forall i. i < 12 ==> c981cr_mask_action c981cr_diagonal (EL i c981ow_masks) =
                  EL (EL i c981da_owner_tr) c981ow_masks`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981da_owner_tr; c981ow_masks] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC C981DA_DIAG_MASKS);;

let C981DA_OWNERMASKS_TRANSPOSE_BACK = prove
 (`forall i. i < 12 ==> c981cr_mask_action c981cr_diagonal (EL (EL i c981da_owner_tr) c981ow_masks) =
                  EL i c981ow_masks`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981da_owner_tr; c981ow_masks] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC C981DA_DIAG_MASKS);;

(* Lean: ownerMasks_candidate *)
let C981DA_OWNERMASKS_CANDIDATE = prove
 (`forall i. i < 12 ==> MEM (EL i c981ow_masks) CANDMASKS`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[c981ow_masks] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[CANDMASKS; MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* the transposed packing's marker codes *)
let C981DA_CODE_RAW = prove
 (`forall c1 c2 a b l (i:num).
     ownmask (c2 i) (c1 i) (b i) (a i) l =
     c981cr_mask_action c981cr_diagonal (ownmask (c1 i) (c2 i) (a i) (b i) l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c981cr_mask_action; C981CR_DIAG_PERM; OWNED_BITSET] THEN
  REWRITE_TAC[ownmask] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC(SPECL [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`;
                          `(b:num->real) i`; `l:real`] OWNED_SW));;

(* Lean: diagonal_ownerIndex *)
let C981DA_DIAGONAL_OWNERINDEX = prove
 (`forall c1 c2 a b l ow. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\
     ow < 12
     ==> oidx c2 c1 b a l (EL ow c981ow_masks) =
         oidx c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C981CR_DIAGONAL_PACKING_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k = oidx c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks)` THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `ccc981ri_family`; `EL (EL ow c981da_owner_tr) c981ow_masks`] OO_CODE) THEN
  ASM_SIMP_TAC[C981OW_OWNERMASKS_MEM; C981DA_OWNER_TR_LT] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`;
                `ccc981ri_family`; `EL ow c981ow_masks`] OO_CODE) THEN
  ASM_SIMP_TAC[C981OW_OWNERMASKS_MEM] THEN STRIP_TAC THEN
  MATCH_MP_TAC OWNMASK_INJ THEN
  MAP_EVERY EXISTS_TAC [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[C981DA_CODE_RAW] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C981DA_OWNERMASKS_TRANSPOSE_BACK]);;

(* Lean: diagonal_auxiliary_mem *)
let C981DA_DIAGONAL_AUXILIARY_MEM = prove
 (`forall c1 c2 a b l ow j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\
     ow < 12 /\ j < 20
     ==> (j IN ooaux c2 c1 b a l (EL ow c981ow_masks) <=>
          EL j c981da_aux_tr IN ooaux c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ooaux] THEN
  ASM_SIMP_TAC[C981DA_DIAGONAL_OWNERINDEX] THEN
  ABBREV_TAC `k = oidx c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks)` THEN
  ASM_SIMP_TAC[GSYM PK_COMBINED_EXACT; C981DA_AUX_TR_LT] THEN
  REWRITE_TAC[C981CR_SWAP_LINSIDE] THEN
  ASM_SIMP_TAC[C981DA_AUXILIARYTRANSPOSE_POINT]);;

(* Lean: diagonal_auxiliary_eq *)
let C981DA_DIAGONAL_AUXILIARY_EQ = prove
 (`forall c1 c2 a b l ow sa sb. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\
     ow < 12 /\ sb SUBSET {j | j < 20} /\
     (forall j. j < 20 ==> (EL j c981da_aux_tr IN sa <=> j IN sb)) /\
     ooaux c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks) = sa
     ==> ooaux c2 c1 b a l (EL ow c981ow_masks) = sb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j < 20` THENL
   [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `ow:num`; `j:num`] C981DA_DIAGONAL_AUXILIARY_MEM) THEN
    ASM_SIMP_TAC[];
    MP_TAC(SPECL [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`;
                  `EL ow c981ow_masks`] (REWRITE_RULE[C981DA_AUXOWN_SUBSET20]
      (prove(`forall c1 c2 a b l m. ooaux c1 c2 a b l m SUBSET {j | j < 20}`,
             REWRITE_TAC[ooaux; C981DA_AUXOWN_SUBSET20])))) THEN
    UNDISCH_TAC `sb SUBSET {j | j < 20}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* Lean: diagonal_auxiliary_subset *)
let C981DA_DIAGONAL_AUXILIARY_SUBSET = prove
 (`forall c1 c2 a b l ow sa sb. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\
     ow < 12 /\ sb SUBSET {j | j < 20} /\
     (forall j. j < 20 ==> (EL j c981da_aux_tr IN sa <=> j IN sb)) /\
     sa SUBSET ooaux c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks)
     ==> sb SUBSET ooaux c2 c1 b a l (EL ow c981ow_masks)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j < 20` ASSUME_TAC THENL
   [UNDISCH_TAC `sb SUBSET {j | j < 20}` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `ow:num`; `j:num`] C981DA_DIAGONAL_AUXILIARY_MEM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `sa SUBSET ooaux c1 c2 a b l (EL (EL ow c981da_owner_tr) c981ow_masks)` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let C981DA_EL_FACTS = prove
 (`EL 8 c981ow_masks = 4096 /\ EL 8 c981da_owner_tr = 9 /\ EL 9 c981ow_masks = 8192`,
  REWRITE_TAC[c981ow_masks; c981da_owner_tr] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* Lean: diagonal_left_owner *)
let C981DA_DIAGONAL_LEFT_OWNER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> oidx c2 c1 b a l 4096 = oidx c1 c2 a b l 8192`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `8`]
    C981DA_DIAGONAL_OWNERINDEX) THEN
  ASM_REWRITE_TAC[C981DA_EL_FACTS] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: diagonal_pattern *)
let C981DA_DIAGONAL_PATTERN = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\
     ooaux c1 c2 a b l 8192 = {4, 6, 15}
     ==> ooaux c2 c1 b a l 4096 = {1, 11, 13}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `8`;
                `{4, 6, 15}`; `{1, 11, 13}`] C981DA_DIAGONAL_AUXILIARY_EQ) THEN
  REWRITE_TAC[C981DA_EL_FACTS] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[C981DA_AUXILIARYTRANSPOSE_PATTERN] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN ARITH_TAC);;
