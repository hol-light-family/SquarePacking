(* ========================================================================= *)
(* Phase 2: Completion/Cases/C981/CornerReduction.lean.                      *)
(* Diagonal symmetry reduction of case 981 to one missing-corner branch.     *)
(* A Lean Transform <swap, reflectX, reflectY> is a triple bool#bool#bool;   *)
(* S12.allTransforms is c981cr_all_transforms;  Transform.markerAction t is  *)
(* the Phase-1 marker permutation dperm (row 4*swap + 2*reflectX + reflectY  *)
(* of MPERMS, which is Lean's markerPerms in allTransforms order:            *)
(* FamilyTransport.transform_rows_match);  Transform.maskAction t m is       *)
(* binarysum (IMAGE (markerAction t) (bitset m)) (Lean permuteMask, equal on *)
(* 16-bit masks).  diagonal.pullPacking p of the packing (c1,c2,a,b,l) is    *)
(* the packing (c2,c1,b,a,l) (transport.ml NPACK_SW: its squares are the     *)
(* pullSwap of the old squares, OSQ_MAP_SW).  ExactMarkers / packing squares *)
(* as in CornerRoots.ml.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/CC_C981_Geometry.ml";;

(* Lean: S12.allTransforms *)
let c981cr_all_transforms = new_definition
 `c981cr_all_transforms : (bool#bool#bool)list =
    [(false,false,false); (false,false,true); (false,true,false); (false,true,true); (true,false,false); (true,false,true); (true,true,false); (true,true,true)]`;;

(* Lean: S12.Transform.markerAction (through markerPerms) *)
let c981cr_marker_action = new_definition
 `c981cr_marker_action (g:bool#bool#bool) (k:num) =
    dperm ((if FST g then 4 else 0) + (if FST (SND g) then 2 else 0) + (if SND (SND g) then 1 else 0)) k`;;

(* Lean: S12.Transform.maskAction *)
let c981cr_mask_action = new_definition
 `c981cr_mask_action (g:bool#bool#bool) (m:num) = binarysum (IMAGE (c981cr_marker_action g) (bitset m))`;;

(* Lean: diagonal *)
let c981cr_diagonal = new_definition `c981cr_diagonal = (true,false,false)`;;

(* Lean: diagonal_mem *)
let C981CR_DIAGONAL_MEM = prove
 (`MEM c981cr_diagonal c981cr_all_transforms`,
  REWRITE_TAC[c981cr_diagonal; c981cr_all_transforms; MEM; PAIR_EQ]);;

let C981CR_DIAG_PERM = prove
 (`c981cr_marker_action c981cr_diagonal = (\k. EL k [1;0;7;6;5;4;3;2;8;11;10;9;13;12;15;14])`,
  REWRITE_TAC[FUN_EQ_THM; c981cr_marker_action; c981cr_diagonal; dperm; MPERMS] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* the diagonal mask action on a literal mask m *)
let c981cr_diag_mask m =
  let tm = mk_comb(`c981cr_mask_action c981cr_diagonal`, mk_small_numeral m) in
  let m' = itlist (fun i acc -> acc + (1 lsl (List.nth [1;0;7;6;5;4;3;2;8;11;10;9;13;12;15;14] i))) (bits m) 0 in
  let th1 = (REWRITE_CONV[c981cr_mask_action; C981CR_DIAG_PERM; bitset_bits m; GSYM SET_OF_LIST_MAP; MAP] THENC
             DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV EL_CONV) tm in
  let eq = prove(mk_eq(rand (rhs (concl th1)), rand (lhand (concl (binarysum_bits m')))),
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM] THEN ARITH_TAC) in
  TRANS th1 (TRANS (AP_TERM `binarysum` eq) (binarysum_bits m'));;

let C981CR_FAMILY_LIST = [1; 2; 12; 48; 192; 512; 1024; 2048; 4096; 8192; 16384; 32768];;

(* Lean: diagonal_family *)
let C981CR_DIAGONAL_FAMILY = prove
 (`IMAGE (c981cr_mask_action c981cr_diagonal) ccc981ri_family = ccc981ri_family`,
  REWRITE_TAC[ccc981ri_family; IMAGE_CLAUSES] THEN
  REWRITE_TAC(map c981cr_diag_mask C981CR_FAMILY_LIST) THEN
  CONV_TAC setlit_eq_dconv);;

let C981CR_FFP_BITSET = prove
 (`forall c1 c2 a b l G. G IN FFP c1 c2 a b l ==> G = bitset (binarysum G)`,
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM ownmask; OWNED_BITSET]);;

(* Lean: diagonal_packing_family *)
let C981CR_DIAGONAL_PACKING_FAMILY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> NPACK c2 c1 b a l /\ IMAGE binarysum (FFP c2 c1 b a l) = ccc981ri_family`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NPACK_SW) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM C981CR_DIAGONAL_FAMILY] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ_ON THEN
  X_GEN_TAC `G:num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; c981cr_mask_action; C981CR_DIAG_PERM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC C981CR_FFP_BITSET THEN ASM_MESON_TAC[]);;

(* the transposed packing's squares: Inside at (x, y) is the old Inside at (y, x) *)
let C981CR_SWAP_LINSIDE = prove
 (`forall c1 c2 a b l (i:num) x y.
     linside (b i) (a i) (b i * c2 i + a i * c1 i - l / &2) (--a i * c2 i + b i * c1 i - l / &2) l x y <=>
     linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* the marker set of a transposed square *)
let C981CR_SWAP_EXACT = prove
 (`forall c1 c2 a b l (j:num). ownmask (c1 j) (c2 j) (a j) (b j) l = 2
     ==> forall k. k < 16 ==> (linside (b j) (a j) (b j * c2 j + a j * c1 j - l / &2) (--a j * c2 j + b j * c1 j - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`; `j:num`]
    C977CR_CODED_EXACT) THEN
  REWRITE_TAC[OWNED_BITSET] THEN
  ONCE_REWRITE_TAC[OWNED_SW] THEN REWRITE_TAC[GSYM OWNED_BITSET] THEN
  ASM_REWRITE_TAC[bitset_bits 2; GSYM SET_OF_LIST_MAP; MAP] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[set_of_list]);;

(* Lean: missing_corner_normal_form *)
let C981CR_MISSING_CORNER_NORMAL_FORM = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> exists d1 d2 e1 e2. NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc981ri_family /\
           exists i. i < 12 /\
               (forall k. k < 16 ==> (linside (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2) (--e2 i * d1 i + e1 i * d2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})) /\
               ~linside (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2) (--e2 i * d1 i + e1 i * d2 i - l / &2) l (&1) (&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C981G_CORNER_OWNERS) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `i:num`; `j:num`] NPACK_LDISJ) THEN
  ASM_REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&1`; `&1`]) THEN
  ASM_CASES_TAC `linside ((a:num->real) i) ((b:num->real) i) (a i * (c1:num->real) i + b i * (c2:num->real) i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)` THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
      C981CR_DIAGONAL_PACKING_FAMILY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN
    ASM_SIMP_TAC[C981CR_SWAP_EXACT; C981CR_SWAP_LINSIDE];
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

(* Lean: excludes_case_iff_missing_corner *)
let C981CR_EXCLUDES_CASE_IFF_MISSING_CORNER = prove
 (`excl_case 981 <=>
   forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> forall i. i < 12 ==>
             (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})) ==>
             ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) ==> false`,
  REWRITE_TAC[CCC981RI_EXCLUDES_CASE_IFF; excl_fam] THEN EQ_TAC THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
      C981CR_MISSING_CORNER_NORMAL_FORM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
