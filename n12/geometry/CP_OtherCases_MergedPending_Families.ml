(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/Families.lean        *)
(* (namespace N12Compact.MergedPending; Lean header: "Source only,           *)
(* uncompiled").  Original entrances for C683, C700 and C867.               *)
(* Lean Case (c683 | c700 | c867) and family k: one HOL family constant per  *)
(* case (mpf_family_c683 / _c700 / _c867), MPF_FAMILIES lists them in Lean   *)
(* order; per-case Lean theorems become OCaml lists of theorems in the same  *)
(* order (Lean "forall k" = each list entry).  WallData p is the predicate   *)
(* mpf_wallData c1 c2 a b l (its nine fields as a conjunction).              *)
(* owner p m = (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l.               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_OriginalWalls.ml";;

(* Lean: Case, family *)
let mpf_family_c683 = new_definition
 `mpf_family_c683 = {1,2,12,16,32,192,256,512,3072,4096,8192,32768}`;;
let mpf_family_c700 = new_definition
 `mpf_family_c700 = {1,2,12,16,32,192,256,1536,4096,8192,16384,32768}`;;
let mpf_family_c867 = new_definition
 `mpf_family_c867 = {1,2,12,16,192,256,512,3072,4096,8192,16384,32768}`;;
let MPF_FAMILIES = [`mpf_family_c683`; `mpf_family_c700`; `mpf_family_c867`];;
let MPF_FAMILY_DEFS = [mpf_family_c683; mpf_family_c700; mpf_family_c867];;

(* Lean: common_member (one theorem per case) *)
let MPF_COMMON_MEMBER = map (fun def ->
  let fam = lhs (concl def) in
  prove
   (mk_forall(`m:num`, mk_imp(`m IN {1,2,12,16,192,256,4096,8192,32768}`,
      mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `m:num`), fam))),
    REWRITE_TAC[def; IN_INSERT; NOT_IN_EMPTY] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV)) MPF_FAMILY_DEFS;;

(* Lean: WallData (structure) *)
let mpf_wallData = new_definition
 `mpf_wallData c1 c2 a b l <=>
    (forall x. &28 / &25 <= x /\ x <= &87 / &50
         ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1)
                     (oov c1 c2 a b l 1) l x (&1)) /\
    (forall y. &28 / &25 <= y /\ y <= &87 / &50
         ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2)
                     (oov c1 c2 a b l 2) l (&1) y) /\
    (forall x. &113 / &50 <= x /\ x <= &72 / &25
         ==> linside (ooc c1 c2 a b l 16) (oos c1 c2 a b l 16) (oou c1 c2 a b l 16)
                     (oov c1 c2 a b l 16) l x (&3)) /\
    &2 < lcy (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096)
             (oov c1 c2 a b l 4096) l /\
    (forall y. &111 / &50 <= y /\ y <= &239 / &100
         ==> linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096)
                     (oov c1 c2 a b l 4096) l (&1) y) /\
    &2 < lcx (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
             (oov c1 c2 a b l 8192) l /\
    (forall x. &111 / &50 <= x /\ x <= &239 / &100
         ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                     (oov c1 c2 a b l 8192) l x (&1)) /\
    lcx (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
        (oov c1 c2 a b l 32768) l < &2 /\
    (forall x. &161 / &100 <= x /\ x <= &89 / &50
         ==> linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                     (oov c1 c2 a b l 32768) l x (&3))`;;

(* the walls for any family containing the common members *)
let MPF_WALLS_GEN = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     (forall m. m IN {1,2,12,16,192,256,4096,8192,32768} ==> m IN fam)
     ==> mpf_wallData c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun m -> SUBGOAL_THEN (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`,
      mk_small_numeral m), `fam:num->bool`)) ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC]) [1; 2; 16; 4096; 8192; 32768] THEN
  REWRITE_TAC[mpf_wallData] THEN
  MP_TAC(SPECL OO_VARS MPOW_LEFT_WALL) THEN
  MP_TAC(SPECL OO_VARS MPOW_BOTTOM_WALL) THEN
  MP_TAC(SPECL OO_VARS MPOW_TOP_WALL) THEN
  MP_TAC(SPECL OO_VARS MPSB_SINGLETON_BOTTOM) THEN
  MP_TAC(SPECL OO_VARS MPSB_SINGLETON_LEFT) THEN
  MP_TAC(SPECL OO_VARS MPSB_SINGLETON_TOP) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Lean: walls (one theorem per case) *)
let MPF_WALLS = map2 (fun fam cm ->
  prove
   (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)),
             `mpf_wallData c1 c2 a b l`))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MPF_WALLS_GEN THEN
    EXISTS_TAC fam THEN ASM_REWRITE_TAC[cm])) MPF_FAMILIES MPF_COMMON_MEMBER;;

(* Lean: c683_right_singleton *)
let MPF_C683_RIGHT_SINGLETON = oo_inst `mpf_family_c683` MPSB_SINGLETON_RIGHT;;

(* Lean: c700_right_singleton *)
let MPF_C700_RIGHT_SINGLETON = oo_inst `mpf_family_c700` MPSB_SINGLETON_RIGHT;;

(* Lean: c700_right_wall *)
let MPF_C700_RIGHT_WALL = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = mpf_family_c700
     ==> lcy (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
             (oov c1 c2 a b l 16384) l < &2 /\
         forall y. &161 / &100 <= y /\ y <= &89 / &50
             ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
                         (oov c1 c2 a b l 16384) l (&3) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MPOW_RIGHT_WALL THEN
  EXISTS_TAC `mpf_family_c700` THEN
  ASM_REWRITE_TAC[in_fam 16384 `mpf_family_c700`; in_fam 32 `mpf_family_c700`]);;

(* Lean: upper_merged_markers (generic in the family; MPF_UPPER_MERGED_MARKERS lists the
   per-case instances, each keeping the hypothesis 3072 IN family k) *)
let MPF_UPPER_MERGED_MARKERS_GEN = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ 3072 IN fam
     ==> linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                 (oov c1 c2 a b l 3072) l (&33 / &20) (&47 / &20) /\
         linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                 (oov c1 c2 a b l 3072) l (&47 / &20) (&47 / &20)`,
  SIMP_TAC[oo_seed 3072 (`&33 / &20`, `&47 / &20`); oo_seed 3072 (`&47 / &20`, `&47 / &20`)]);;
let MPF_UPPER_MERGED_MARKERS =
  map (fun fam -> GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
         (SPEC fam (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
            MPF_UPPER_MERGED_MARKERS_GEN))) MPF_FAMILIES;;

(* Lean: c700_merged_markers *)
let MPF_C700_MERGED_MARKERS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = mpf_family_c700
     ==> linside (ooc c1 c2 a b l 1536) (oos c1 c2 a b l 1536) (oou c1 c2 a b l 1536)
                 (oov c1 c2 a b l 1536) l (&47 / &20) (&33 / &20) /\
         linside (ooc c1 c2 a b l 1536) (oos c1 c2 a b l 1536) (oou c1 c2 a b l 1536)
                 (oov c1 c2 a b l 1536) l (&47 / &20) (&47 / &20)`,
  SIMP_TAC[oo_inst `mpf_family_c700` (oo_seed 1536 (`&47 / &20`, `&33 / &20`));
           oo_inst `mpf_family_c700` (oo_seed 1536 (`&47 / &20`, `&47 / &20`))]);;
