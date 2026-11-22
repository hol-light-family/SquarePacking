(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/WallBranches.lean.                         *)
(* Conventions of MissingCornerPoints.ml.  Fin 4 -> Nat wallCode is          *)
(* c977wb_wallcode k (k < 4);  a WallOwners p structure is an index function *)
(* w : num -> num with c977wb_owners c1 c2 a b l w;  wallCoordinate is       *)
(* c977wb_coord;  a WallBranch (Fin 4 -> Bool) is a function bb : num->bool  *)
(* of which only bb 0..bb 3 matter (canonical representatives: bb k = F for  *)
(* k >= 4, counted in wall_branch_count);  WallHalfSpaces is c977wb_half.    *)
(* Owns q 10 is linside q (marker 10$1) (marker 10$2).  Tag C977WB_.         *)
(* ========================================================================= *)

needs "n12/geometry/MissingCornerPoints.ml";;

(* Lean: wallCode *)
let c977wb_wallcode = new_definition
 `c977wb_wallcode (k:num) = EL k [4096; 8192; 16384; 32768]`;;

let C977WB_LT4 = ARITH_RULE `(k:num) < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`;;

let C977WB_WALLCODE_CASES = prove
 (`c977wb_wallcode 0 = 4096 /\ c977wb_wallcode 1 = 8192 /\
   c977wb_wallcode 2 = 16384 /\ c977wb_wallcode 3 = 32768`,
  REWRITE_TAC[c977wb_wallcode] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Lean: wall_code_mem *)
let C977WB_WALL_CODE_MEM = prove
 (`forall k. k < 4 ==> c977wb_wallcode k IN ccc977ri_family`,
  REWRITE_TAC[C977WB_LT4] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[C977WB_WALLCODE_CASES; ccc977ri_family; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Lean: wall_code_injective *)
let C977WB_WALL_CODE_INJECTIVE = prove
 (`forall k l. k < 4 /\ l < 4 /\ c977wb_wallcode k = c977wb_wallcode l ==> k = l`,
  REWRITE_TAC[C977WB_LT4] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[C977WB_WALLCODE_CASES] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: WallOwners (structure) *)
let c977wb_owners = new_definition
 `c977wb_owners (c1:num->real) c2 a b l (w:num->num) <=>
    forall k. k < 4 ==> w k < 12 /\
                  ownmask (c1 (w k)) (c2 (w k)) (a (w k)) (b (w k)) l = c977wb_wallcode k`;;

(* Lean: WallOwners.index_injective *)
let C977WB_INDEX_INJECTIVE = prove
 (`forall c1 c2 a b l w. c977wb_owners c1 c2 a b l w
     ==> forall k k'. k < 4 /\ k' < 4 /\ w k = w k' ==> k = k'`,
  REWRITE_TAC[c977wb_owners] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C977WB_WALL_CODE_INJECTIVE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `k:num` th) THEN MP_TAC(SPEC `k':num` th)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let C977WB_CODE_IN_IMAGE = prove
 (`forall c1 c2 a b l i. i < 12
     ==> ownmask (c1 i) (c2 i) (a i) (b i) l IN IMAGE binarysum (FFP c1 c2 a b l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `owned ((c1:num->real) i) ((c2:num->real) i) ((a:num->real) i) ((b:num->real) i) l` THEN
  REWRITE_TAC[ownmask; FFP; IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]);;

(* Lean: wall_owners *)
let C977WB_WALL_OWNERS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists w. c977wb_owners c1 c2 a b l w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c977wb_owners; GSYM RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977wb_wallcode k`] C977CR_CODE_OWNER_UNIQUE) THEN
  ASM_SIMP_TAC[C977WB_WALL_CODE_MEM] THEN MESON_TAC[]);;

(* Lean: wallCoordinate *)
let c977wb_coord = new_definition
 `c977wb_coord (c1:num->real) c2 a b l (w:num->num) (k:num) =
    if k MOD 2 = 0
    then lcy (a (w k)) (b (w k)) (a (w k) * c1 (w k) + b (w k) * c2 (w k) - l / &2)
             (--b (w k) * c1 (w k) + a (w k) * c2 (w k) - l / &2) l
    else lcx (a (w k)) (b (w k)) (a (w k) * c1 (w k) + b (w k) * c2 (w k) - l / &2)
             (--b (w k) * c1 (w k) + a (w k) * c2 (w k) - l / &2) l`;;

(* Lean: WallHalfSpaces *)
let c977wb_half = new_definition
 `c977wb_half (c1:num->real) c2 a b l (w:num->num) (bb:num->bool) <=>
    forall k. k < 4 ==> (if bb k then c977wb_coord c1 c2 a b l w k <= &2
                   else &2 <= c977wb_coord c1 c2 a b l w k)`;;

(* Lean: wall_branch_count *)
let C977WB_WALL_BRANCH_COUNT = prove
 (`CARD {bb:num->bool | forall k. ~(k < 4) ==> bb k = false} = 16`,
  MP_TAC(ISPECL [`false`; `2`; `(:bool)`; `4`; `{k:num | k < 4}`] HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_LT; HAS_SIZE_BOOL; IN_UNIV; IN_ELIM_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[HAS_SIZE]);;

(* Lean: closed_wall_branch_cover *)
let C977WB_CLOSED_WALL_BRANCH_COVER = prove
 (`forall c1 c2 a b l w. c977wb_owners c1 c2 a b l w ==> exists bb. c977wb_half c1 c2 a b l w bb`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\k. c977wb_coord c1 c2 a b l w k <= &2` THEN
  REWRITE_TAC[c977wb_half] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: wall_split_tie *)
let C977WB_WALL_SPLIT_TIE = prove
 (`forall c1 c2 a b l w k. c977wb_owners c1 c2 a b l w /\ k < 4 /\ c977wb_coord c1 c2 a b l w k = &2
     ==> forall choice. if choice then c977wb_coord c1 c2 a b l w k <= &2
                  else &2 <= c977wb_coord c1 c2 a b l w k`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; COND_ID]);;

(* Lean: case_wall_branch_cover *)
let C977WB_CASE_WALL_BRANCH_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists w. c977wb_owners c1 c2 a b l w /\ exists bb. c977wb_half c1 c2 a b l w bb`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WB_WALL_OWNERS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  MESON_TAC[C977WB_CLOSED_WALL_BRANCH_COVER]);;

(* Lean: unused_marker_ten *)
let C977WB_UNUSED_MARKER_TEN = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12
     ==> ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                  (--b i * c1 i + a i * c2 i - l / &2) l (marker 10$1) (marker 10$2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977WB_CODE_IN_IMAGE) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODED_EXACT) THEN
  DISCH_THEN(MP_TAC o SPEC `10`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`ownmask (c1 i) (c2 i) (a i) (b i) l`, `m:num`) THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[ccc977ri_family; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC(map bitset_bits [1; 2; 12; 48; 192; 256; 512; 2048; 4096; 8192; 16384; 32768]) THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;
