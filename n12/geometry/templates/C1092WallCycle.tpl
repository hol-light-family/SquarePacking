(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallCycle.lean (Lean header: "Source-only:   *)
(* this module has not been replayed").                                      *)
(* Original C1092 ownership to four simultaneous wall barriers.             *)
(* Lean  owners p i = p.square (ownerIndex p (ownerCode i))  is the          *)
(* OriginalOwners owner 5-tuple at mask  EL i c1092wc_code.                  *)
(* wallOwner / centralOwner / cornerOwner / cornerPoint are the HOL lists    *)
(* c1092wc_wall / central / corner / cpoint (k < 4, EL k).                   *)
(* localFrame k q is the 5-tuple c1092wc_lf{c,s,u,v} k c s u v a (side a);   *)
(* wallFrame p k is c1092wc_wf{c,s,u,v} c1 c2 a b l k (side l); pointMap is *)
(* c1092wc_pm{x,y}; branchY is c1092wc_by; forcedPoint is c1092wc_fp{x,y};  *)
(* a WallBranch Fin 4 -> Bool is br:num->bool; WallContext p b is            *)
(* c1092wc_ctx c1 c2 a b l br.  S12.Owns is c1092wphy_owns.  The private      *)
(* markerMap/local_owns are replaced by a direct marker computation in       *)
(* frame_singleton.  S12.Convex.inside_segment is C1092WC_INSIDE_SEGMENT;     *)
(* ClosedPointExclusion.outside_of_closed is OUTSIDE_OF_CLOSED (p2_base).     *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/C1092WallPhysical.ml";;

(* Lean: family, ownerCode *)
let c1092wc_family = new_definition
 `c1092wc_family = {3,12,48,192,256,512,1024,2048,4096,8192,16384,32768}`;;
let c1092wc_code = new_definition
 `c1092wc_code = [3;12;48;192;256;512;1024;2048;4096;8192;16384;32768]`;;

(* Lean: wallOwner, centralOwner, cornerOwner, cornerPoint *)
let c1092wc_wall = new_definition `c1092wc_wall = [8;9;10;11]`;;
let c1092wc_central = new_definition `c1092wc_central = [4;5;6;7]`;;
let c1092wc_corner = new_definition `c1092wc_corner = [0;1;2;3]`;;
let c1092wc_cpoint = new_definition
 `c1092wc_cpoint = [(&1, &1); (&3, &1); (&3, &3); (&1, &3)]`;;

let C1092WC_CODE_EL = el_lookups c1092wc_code;;
let C1092WC_WALL_ELS = el_lookups c1092wc_wall;;
let C1092WC_CENTRAL_ELS = el_lookups c1092wc_central;;
let C1092WC_CORNER_ELS = el_lookups c1092wc_corner;;
let C1092WC_CPOINT_ELS = el_lookups c1092wc_cpoint;;
let C1092WC_LISTS = Array.to_list C1092WC_CODE_EL @ Array.to_list C1092WC_WALL_ELS @
  Array.to_list C1092WC_CENTRAL_ELS @ Array.to_list C1092WC_CORNER_ELS @ Array.to_list C1092WC_CPOINT_ELS;;

let C1092WC_INDEX = prove
 (`!k. k < 4 ==> EL k c1092wc_wall = k + 8 /\ EL k c1092wc_central = k + 4 /\
                 EL k c1092wc_corner = k`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN
  REWRITE_TAC C1092WC_LISTS THEN CONV_TAC NUM_REDUCE_CONV);;

let C1092WC_IDX_TAC =
  ASM_SIMP_TAC[C1092WC_INDEX] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binop `(<):num->num->bool` (concl th)))) THEN
  ARITH_TAC;;

let C1092WC_LIST = oo_list_facts `c1092wc_family` (rand (concl c1092wc_code));;
let C1092WC_LENGTH = (REWRITE_CONV[c1092wc_code; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c1092wc_code`;;

let C1092WC_MEMBER = prove
 (`!i. i < 12 ==> EL i c1092wc_code IN c1092wc_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C1092WC_LENGTH; c1092wc_code] THEN ASM_REWRITE_TAC[fst C1092WC_LIST]);;

(* Lean: owner_code *)
let C1092WC_OWNER_CODE = prove
 (`!c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\ i < 12
     ==> ownmask (c1 (oidx c1 c2 a b l (EL i c1092wc_code))) (c2 (oidx c1 c2 a b l (EL i c1092wc_code)))
                 (a (oidx c1 c2 a b l (EL i c1092wc_code))) (b (oidx c1 c2 a b l (EL i c1092wc_code))) l =
         EL i c1092wc_code`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c1092wc_family`; `EL i c1092wc_code`] OO_CODE) THEN
  ASM_SIMP_TAC[C1092WC_MEMBER]);;

(* Lean: owners_markers  (ExactMarkers q S: q owns marker k iff k IN S) *)
let C1092WC_OWNERS_MARKERS = prove
 (`!c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\ i < 12
     ==> !k. k < 16 ==> (linside OWN(EL i c1092wc_code) (marker k$1) (marker k$2) <=>
                         k IN bitset (EL i c1092wc_code))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_MARKERS THEN
  EXISTS_TAC `c1092wc_family` THEN ASM_SIMP_TAC[C1092WC_MEMBER]);;

(* Lean: owners_disjoint *)
let C1092WC_OWNERS_DISJOINT = prove
 (`!c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj OWN(EL i c1092wc_code) OWN(EL j c1092wc_code)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c1092wc_family` THEN
  ASM_REWRITE_TAC[C1092WC_LENGTH] THEN REWRITE_TAC[c1092wc_code] THEN
  REWRITE_TAC[fst C1092WC_LIST; snd C1092WC_LIST]);;

(* Lean: corner_points *)
let C1092WC_CORNER_POINTS =
  let seeds = map (fun (m, p) -> oo_inst `c1092wc_family` (oo_seed m p))
    [3, (`&1`, `&1`); 12, (`&3`, `&1`); 48, (`&3`, `&3`); 192, (`&1`, `&3`)] in
  prove
 (`!c1 c2 a b l k. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\ k < 4
     ==> linside OWN(EL (EL k c1092wc_corner) c1092wc_code)
                 (FST (EL k c1092wc_cpoint)) (SND (EL k c1092wc_cpoint))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN
  REWRITE_TAC C1092WC_LISTS THEN ASM_MESON_TAC seeds);;

(* Lean: localFrame, pointMap *)
let c1092wc_lfc = new_definition
 `c1092wc_lfc (k:num) (c:real) (s:real) (u:real) (v:real) (a:real) =
    if k = 0 then c else if k = 1 then s else if k = 2 then --c else --s`;;
let c1092wc_lfs = new_definition
 `c1092wc_lfs (k:num) (c:real) (s:real) (u:real) (v:real) (a:real) =
    if k = 0 then s else if k = 1 then c else if k = 2 then s else c`;;
let c1092wc_lfu = new_definition
 `c1092wc_lfu (k:num) (c:real) (s:real) (u:real) (v:real) (a:real) =
    if k = 0 then u else if k = 1 then u else if k = 2 then u - &4 * c else u - &4 * s`;;
let c1092wc_lfv = new_definition
 `c1092wc_lfv (k:num) (c:real) (s:real) (u:real) (v:real) (a:real) =
    if k = 0 then v else if k = 1 then --v - a else if k = 2 then --v - a - &4 * s
    else --(--v - a) - a - &4 * c`;;
let c1092wc_pmx = new_definition
 `c1092wc_pmx (k:num) (x:real) (y:real) =
    if k = 0 then x else if k = 1 then y else if k = 2 then &4 - x else y`;;
let c1092wc_pmy = new_definition
 `c1092wc_pmy (k:num) (x:real) (y:real) =
    if k = 0 then y else if k = 1 then x else if k = 2 then y else &4 - x`;;

(* Lean: local_inside *)
let C1092WC_LOCAL_INSIDE = prove
 (`!k c s u v a x y. k < 4
     ==> (linside (c1092wc_lfc k c s u v a) (c1092wc_lfs k c s u v a) (c1092wc_lfu k c s u v a)
                  (c1092wc_lfv k c s u v a) a x y <=>
          linside c s u v a (c1092wc_pmx k x y) (c1092wc_pmy k x y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN
  REWRITE_TAC[c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv; c1092wc_pmx; c1092wc_pmy] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_CLAUSES; linside] THEN REAL_ARITH_TAC);;

(* Lean: wallFrame *)
let c1092wc_wfc = new_definition
 `c1092wc_wfc (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (k:num) =
    c1092wc_lfc k OWNW(k)`;;
let c1092wc_wfs = new_definition
 `c1092wc_wfs (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (k:num) =
    c1092wc_lfs k OWNW(k)`;;
let c1092wc_wfu = new_definition
 `c1092wc_wfu (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (k:num) =
    c1092wc_lfu k OWNW(k)`;;
let c1092wc_wfv = new_definition
 `c1092wc_wfv (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (k:num) =
    c1092wc_lfv k OWNW(k)`;;

let C1092WC_WALL_FRAME_INSIDE = prove
 (`!c1 c2 a b l k x y. k < 4
     ==> (linside WF(k) x y <=> linside OWNW(k) (c1092wc_pmx k x y) (c1092wc_pmy k x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv] THEN
  MATCH_MP_TAC C1092WC_LOCAL_INSIDE THEN ASM_REWRITE_TAC[]);;

(* Lean: frame_side (private; the side is l), frame_box (private), and the unit normal *)
let C1092WC_FRAME_BOX = prove
 (`!c1 c2 a b l k. NPACK c1 c2 a b l /\ k < 4
     ==> c1092wc_wfc c1 c2 a b l k * c1092wc_wfc c1 c2 a b l k +
         c1092wc_wfs c1 c2 a b l k * c1092wc_wfs c1 c2 a b l k = &1 /\
         lcont WF(k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `EL (EL k c1092wc_wall) c1092wc_code`] OO_UNIT) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `EL (EL k c1092wc_wall) c1092wc_code`] OO_BOX) THEN
  ASM_REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv] THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN
  REWRITE_TAC[c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LCONT_PULLX; LCONT_PULLSW] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* the owned-marker facts of the four wall owners, under the assumptions NPACK and the family *)
let c1092wc_marker_facts =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let fam = `c1092wc_family` in
  let hyp = CONJ (ASSUME `NPACK c1 c2 a b l`)
                 (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`) in
  let one m =
    let mt = mk_small_numeral m in
    let th0 = MP (SPECL (vars @ [fam; mt]) OO_MARKERS) (CONJ (CONJUNCT1 hyp) (CONJ (CONJUNCT2 hyp) (in_fam m fam))) in
    map (fun j ->
      let jt = mk_small_numeral j in
      let th = MP (SPEC jt th0) (EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` jt `16`))) in
      CONV_RULE (REWRITE_CONV[MARKER_EXPLICIT; VECTOR_2; bitset_bits m; IN_SET_OF_LIST; MEM] THENC
                 NUM_REDUCE_CONV THENC REWRITE_CONV[]) th) (0--15) in
  List.concat (map one [4096; 8192; 16384; 32768]);;

(* Lean: frame_singleton *)
let C1092WC_FRAME_SINGLETON = prove
 (`!c1 c2 a b l k j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     k < 4 /\ j < 16
     ==> (c1092wphy_owns WF(k) j <=> j = 12)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[c1092wphy_owns; C1092WC_WALL_FRAME_INSIDE] THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN SPEC_TAC(`j:num`,`j:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC C1092WC_LISTS THEN
  REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; MARKER_EXPLICIT; VECTOR_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC c1092wc_marker_facts);;

(* Lean: branchY, forcedPoint, WallContext *)
let c1092wc_by = new_definition `c1092wc_by (bb:bool) (y:real) = if bb then y else &4 - y`;;
let c1092wc_fpx = new_definition
 `c1092wc_fpx (k:num) (bb:bool) (i:num) =
    c1092wc_pmx k (c1092wp_targetX i) (c1092wc_by bb (c1092wp_targetY i))`;;
let c1092wc_fpy = new_definition
 `c1092wc_fpy (k:num) (bb:bool) (i:num) =
    c1092wc_pmy k (c1092wp_targetX i) (c1092wc_by bb (c1092wp_targetY i))`;;
let c1092wc_ctx = new_definition
 `c1092wc_ctx (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (br:num->bool) <=>
    !k. k < 4
        ==> (if br k then lcy WF(k) <= &2 else &2 <= lcy WF(k)) /\
            !i. i < 12 ==> linside OWNW(k) (c1092wc_fpx k (br k) i) (c1092wc_fpy k (br k) i)`;;

let C1092WC_EACH = prove
 (`!c1 c2 a b l k. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\ k < 4
     ==> ?bb. (if bb then lcy WF(k) <= &2 else &2 <= lcy WF(k)) /\
              !i. i < 12 ==> linside OWNW(k) (c1092wc_fpx k bb i) (c1092wc_fpy k bb i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1092wc_wfc c1 c2 a b l k`; `c1092wc_wfs c1 c2 a b l k`; `c1092wc_wfu c1 c2 a b l k`;
                `c1092wc_wfv c1 c2 a b l k`; `l:real`] C1092WPHY_SINGLETON_WALL_POINT_COVER) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE_LE) THEN
    ASM_SIMP_TAC[C1092WC_FRAME_BOX; C1092WC_FRAME_SINGLETON; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL [EXISTS_TAC `T`; EXISTS_TAC `F`] THEN
  ASM_REWRITE_TAC[c1092wc_fpx; c1092wc_fpy; c1092wc_by] THEN
  ASM_SIMP_TAC[GSYM C1092WC_WALL_FRAME_INSIDE]);;

(* Lean: original_wall_context *)
let C1092WC_ORIGINAL_WALL_CONTEXT = prove
 (`!c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family
     ==> ?br. c1092wc_ctx c1 c2 a b l br`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
    (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C1092WC_EACH)) THEN
  DISCH_THEN(X_CHOOSE_TAC `br:num->bool`) THEN EXISTS_TAC `br:num->bool` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[]);;

(* the wall owner's forced points, from the context *)
let C1092WC_CTX_POINT = prove
 (`!c1 c2 a b l br k i. c1092wc_ctx c1 c2 a b l br /\ k < 4 /\ i < 12
     ==> linside OWNW(k) (c1092wc_fpx k (br k) i) (c1092wc_fpy k (br k) i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[c1092wc_ctx]) THEN
  ASM_SIMP_TAC[]);;

(* Lean: central_missing_points *)
let C1092WC_CENTRAL_MISSING_POINTS = prove
 (`!c1 c2 a b l br j k i.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092wc_ctx c1 c2 a b l br /\ j < 4 /\ k < 4 /\ i < 12
     ==> ~linside OWN(EL (EL j c1092wc_central) c1092wc_code)
                  (c1092wc_fpx k (br k) i) (c1092wc_fpy k (br k) i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `br:num->bool`;
                `k:num`; `i:num`] C1092WC_CTX_POINT) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ldisj OWN(EL (EL j c1092wc_central) c1092wc_code) OWNW(k)` MP_TAC THENL
   [MATCH_MP_TAC C1092WC_OWNERS_DISJOINT THEN C1092WC_IDX_TAC; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]);;

(* Lean: inside_segment (S12.Convex) *)
let C1092WC_INSIDE_SEGMENT = prove
 (`!c s u v a x y x' y' t.
     linside c s u v a x y /\ linside c s u v a x' y' /\ &0 <= t /\ t <= &1
     ==> linside c s u v a ((&1 - t) * x + t * x') ((&1 - t) * y + t * y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((&1 - t) * x + t * x') + s * ((&1 - t) * y + t * y') =
      (&1 - t) * (c * x + s * y) + t * (c * x' + s * y') /\
    --s * ((&1 - t) * x + t * x') + c * ((&1 - t) * y + t * y') =
      (&1 - t) * (--s * x + c * y) + t * (--s * x' + c * y')`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC REAL_CONVEX_BOUND_LT ORELSE MATCH_MP_TAC REAL_CONVEX_BOUND_GT) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: local_wall_segment *)
let C1092WC_LOCAL_WALL_SEGMENT = prove
 (`!c1 c2 a b l br k y.
     c1092wc_ctx c1 c2 a b l br /\ k < 4 /\ &803 / &500 <= y /\ y <= &947 / &500
     ==> linside OWNW(k) (c1092wc_pmx k (&1) (c1092wc_by (br k) y))
                         (c1092wc_pmy k (&1) (c1092wc_by (br k) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linside WF(k) (&1) (c1092wc_by (br k) (&803 / &500)) /\
                linside WF(k) (&1) (c1092wc_by (br k) (&947 / &500))` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `br:num->bool`;
                  `k:num`; `10`] C1092WC_CTX_POINT) THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `br:num->bool`;
                  `k:num`; `11`] C1092WC_CTX_POINT) THEN
    ASM_SIMP_TAC[c1092wc_fpx; c1092wc_fpy; C1092WC_WALL_FRAME_INSIDE; ARITH] THEN
    REWRITE_TAC[c1092wp_targetX; c1092wp_targetY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[COND_CLAUSES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM C1092WC_WALL_FRAME_INSIDE] THEN
  MP_TAC(SPECL [`c1092wc_wfc c1 c2 a b l k`; `c1092wc_wfs c1 c2 a b l k`; `c1092wc_wfu c1 c2 a b l k`;
                `c1092wc_wfv c1 c2 a b l k`; `l:real`;
                `&1`; `c1092wc_by ((br:num->bool) k) (&803 / &500)`; `&1`; `c1092wc_by ((br:num->bool) k) (&947 / &500)`;
                `&125 / &36 * (y - &803 / &500)`] C1092WC_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [REAL_ARITH_TAC; REWRITE_TAC[c1092wc_by] THEN COND_CASES_TAC THEN REAL_ARITH_TAC]);;

(* Lean: wall_auxiliary_point *)
let C1092WC_WALL_AUXILIARY_POINT = prove
 (`!c1 c2 a b l br k.
     c1092wc_ctx c1 c2 a b l br /\ k < 4
     ==> linside OWNW(k) (c1092wc_pmx k (&1) (c1092wc_by (br k) (&87 / &50)))
                         (c1092wc_pmy k (&1) (c1092wc_by (br k) (&87 / &50)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1092WC_LOCAL_WALL_SEGMENT THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: central_missing_segment *)
let C1092WC_CENTRAL_MISSING_SEGMENT = prove
 (`!c1 c2 a b l br j k y.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092wc_ctx c1 c2 a b l br /\ j < 4 /\ k < 4 /\ &803 / &500 <= y /\ y <= &947 / &500
     ==> ~linside OWN(EL (EL j c1092wc_central) c1092wc_code)
                  (c1092wc_pmx k (&1) (c1092wc_by (br k) y)) (c1092wc_pmy k (&1) (c1092wc_by (br k) y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `br:num->bool`;
                `k:num`; `y:real`] C1092WC_LOCAL_WALL_SEGMENT) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ldisj OWN(EL (EL j c1092wc_central) c1092wc_code) OWNW(k)` MP_TAC THENL
   [MATCH_MP_TAC C1092WC_OWNERS_DISJOINT THEN C1092WC_IDX_TAC; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]);;

(* Lean: central_missing_closed_points *)
let C1092WC_CENTRAL_MISSING_CLOSED_POINTS = prove
 (`!c1 c2 a b l br j k i.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092wc_ctx c1 c2 a b l br /\ j < 4 /\ k < 4 /\ i < 12
     ==> ~lclosed OWN(EL (EL j c1092wc_central) c1092wc_code)
                  (c1092wc_fpx k (br k) i) (c1092wc_fpy k (br k) i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `br:num->bool`;
                `k:num`; `i:num`] C1092WC_CTX_POINT) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ldisj OWNW(k) OWN(EL (EL j c1092wc_central) c1092wc_code)` MP_TAC THENL
   [MATCH_MP_TAC C1092WC_OWNERS_DISJOINT THEN C1092WC_IDX_TAC; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_TAC THEN
  MATCH_MP_TAC OUTSIDE_OF_CLOSED THEN
  MAP_EVERY EXISTS_TAC (map (fun f -> mk_comb(f, `EL (EL j c1092wc_central) c1092wc_code`))
    [`ooc c1 c2 a b l`; `oos c1 c2 a b l`; `oou c1 c2 a b l`; `oov c1 c2 a b l`] @ [`l:real`]) THEN
  ASM_SIMP_TAC[OO_UNIT] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: central_missing_closed_corners *)
let C1092WC_CENTRAL_MISSING_CLOSED_CORNERS = prove
 (`!c1 c2 a b l j k.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\ j < 4 /\ k < 4
     ==> ~lclosed OWN(EL (EL j c1092wc_central) c1092wc_code)
                  (FST (EL k c1092wc_cpoint)) (SND (EL k c1092wc_cpoint))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `k:num`] C1092WC_CORNER_POINTS) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ldisj OWN(EL (EL k c1092wc_corner) c1092wc_code) OWN(EL (EL j c1092wc_central) c1092wc_code)`
    MP_TAC THENL
   [MATCH_MP_TAC C1092WC_OWNERS_DISJOINT THEN C1092WC_IDX_TAC; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_TAC THEN
  MATCH_MP_TAC OUTSIDE_OF_CLOSED THEN
  MAP_EVERY EXISTS_TAC (map (fun f -> mk_comb(f, `EL (EL j c1092wc_central) c1092wc_code`))
    [`ooc c1 c2 a b l`; `oos c1 c2 a b l`; `oou c1 c2 a b l`; `oov c1 c2 a b l`] @ [`l:real`]) THEN
  ASM_SIMP_TAC[OO_UNIT] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: excludes_family_of_wall_context *)
let C1092WC_EXCLUDES_FAMILY_OF_WALL_CONTEXT = prove
 (`(!c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family
      ==> !br. c1092wc_ctx c1 c2 a b l br ==> F)
   ==> !c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family ==> F`,
  MESON_TAC[C1092WC_ORIGINAL_WALL_CONTEXT]);;
