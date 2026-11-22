(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/SingletonCorner.lean          *)
(* (N12Compact.Completion.OtherCases.C1089.SingletonCorner).                 *)
(* C1089-LAST-SECTOR-POINTS section 2: the actual singleton owns (1,1).      *)
(* (Lean header: "This source has not been compiled.")                       *)
(* corner_of_seeds: the family q : Fin 12 -> OpenSquare enters through the   *)
(* used squares q 0, 1, 5, 6, 9, 10 (ci si ui vi ai with their invariants);  *)
(* side / same / contained / apart are assumed at the used instances.        *)
(* WallOrigins.right_low / bottom_origin = OC1089WO_RIGHT_LOW / BOTTOM_ORIGIN,*)
(* inside_segment = CES_INSIDE_SEGMENT, C983.C974LocalData.Input =           *)
(* c983ld_input over (q i).translated 1 1 (c983ld_tr), C974LocalEnding.      *)
(* impossible = C983LE_IMPOSSIBLE.  family / masks = c1089sc_family /        *)
(* c1089sc_masks; owners p i = owner (EL i c1089sc_masks), written with the  *)
(* literal mask at fixed indices (owners 0 / 1 / 5 / 6 / 9 / 10 = owner 1 /  *)
(* 12 / 512 / 1024 / 8192 / 16384).  Tag C1089SC_.                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* ~Q x y from ldisj Q R (an assumption) and the assumption R x y *)
let c1089sc_excl d x y =
  let th = SPECL [x; y] (REWRITE_RULE[ldisj] (ASSUME d)) in
  let qa, ra = dest_conj (dest_neg (concl th)) in
  NOT_INTRO (DISCH qa (MP (NOT_ELIM th) (CONJ (ASSUME qa) (ASSUME ra))));;

(* Lean: corner_of_seeds *)
let C1089SC_CORNER_OF_SEEDS = prove
 (`forall c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c5 s5 u5 v5 a5 c6 s6 u6 v6 a6 c9 s9 u9 v9 a9 c10 s10 u10 v10 a10.
     c0 * c0 + s0 * s0 = &1 /\ &0 < a0 /\
     c1 * c1 + s1 * s1 = &1 /\ &0 < a1 /\
     c5 * c5 + s5 * s5 = &1 /\ &0 < a5 /\
     c6 * c6 + s6 * s6 = &1 /\ &0 < a6 /\
     c9 * c9 + s9 * s9 = &1 /\ &0 < a9 /\
     c10 * c10 + s10 * s10 = &1 /\ &0 < a10 /\
     &1 < a0 /\ &1 < a1 /\ &1 < a5 /\ &1 < a6 /\ &1 < a9 /\ &1 < a10 /\
     a0 = a9 /\ a0 = a1 /\ a9 = a1 /\
     lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c9 s9 u9 v9 a9 /\ lcont c10 s10 u10 v10 a10 /\
     ldisj c10 s10 u10 v10 a10 c6 s6 u6 v6 a6 /\
     ldisj c10 s10 u10 v10 a10 c5 s5 u5 v5 a5 /\
     ldisj c1 s1 u1 v1 a1 c10 s10 u10 v10 a10 /\
     ldisj c1 s1 u1 v1 a1 c9 s9 u9 v9 a9 /\
     ldisj c9 s9 u9 v9 a9 c5 s5 u5 v5 a5 /\
     ldisj c9 s9 u9 v9 a9 c10 s10 u10 v10 a10 /\
     ldisj c0 s0 u0 v0 a0 c9 s9 u9 v9 a9 /\
     ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\
     ldisj c9 s9 u9 v9 a9 c1 s1 u1 v1 a1 /\
     linside c0 s0 u0 v0 a0 (&1) (&457 / &500) /\
     linside c0 s0 u0 v0 a0 (&91 / &50) (&1) /\
     linside c0 s0 u0 v0 a0 (&49 / &25) (&19 / &25) /\
     linside c1 s1 u1 v1 a1 (&3) (&457 / &500) /\
     linside c1 s1 u1 v1 a1 (&3) (&1) /\
     linside c5 s5 u5 v5 a5 (&47 / &20) (&33 / &20) /\
     linside c5 s5 u5 v5 a5 (&2) (&3 / &2) /\
     linside c6 s6 u6 v6 a6 (&3) (&113 / &50) /\
     linside c9 s9 u9 v9 a9 (&2) (&457 / &500) /\
     linside c9 s9 u9 v9 a9 (&12 / &5) (&1) /\
     linside c9 s9 u9 v9 a9 (&14 / &5) (&1) /\
     linside c10 s10 u10 v10 a10 (&1543 / &500) (&2) /\
     linside c10 s10 u10 v10 a10 (&3) (&8 / &5)
     ==> linside c0 s0 u0 v0 a0 (&1) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside c10 s10 u10 v10 a10 (&3) (&36 / &25)` ASSUME_TAC THENL
   [MATCH_MP_TAC OC1089WO_RIGHT_LOW THEN
    MAP_EVERY EXISTS_TAC (oc1089wo_sq 6 @ oc1089wo_sq 5) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside c10 s10 u10 v10 a10 (&3) (&3 / &2)` ASSUME_TAC THENL
   [MP_TAC(SPECL (oc1089wo_sq 10 @ [`&3`; `&36 / &25`; `&3`; `&8 / &5`; `&3 / &8`])
      CES_INSIDE_SEGMENT) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside c9 s9 u9 v9 a9 (&2) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC OC1089WO_BOTTOM_ORIGIN THEN
    MAP_EVERY EXISTS_TAC (oc1089wo_sq 1 @ oc1089wo_sq 10) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `linside c0 s0 u0 v0 a0 (&1) (&1)` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun (d, x, y) -> ASSUME_TAC (c1089sc_excl d x y))
   [`ldisj c9 s9 u9 v9 a9 c5 s5 u5 v5 a5`, `&47 / &20`, `&33 / &20`;
    `ldisj c9 s9 u9 v9 a9 c5 s5 u5 v5 a5`, `&2`, `&3 / &2`;
    `ldisj c9 s9 u9 v9 a9 c10 s10 u10 v10 a10`, `&3`, `&3 / &2`;
    `ldisj c1 s1 u1 v1 a1 c10 s10 u10 v10 a10`, `&3`, `&3 / &2`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  MATCH_MP_TAC (SPECL (c983ld_tr (oc1089wo_sq 0) @ c983ld_tr (oc1089wo_sq 9) @
                       c983ld_tr (oc1089wo_sq 1)) C983LE_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         C983LD_CLOSE_TAC []
           [REWRITE_RULE[lcont] (ASSUME `lcont c0 s0 u0 v0 a0`);
            REWRITE_RULE[lcont] (ASSUME `lcont c1 s1 u1 v1 a1`)]]);;

(* Lean: family, masks *)
let c1089sc_family = new_definition
 `c1089sc_family = {1,12,48,192,256,512,1024,2048,4096,8192,16384,32768}`;;
let c1089sc_masks = new_definition
 `c1089sc_masks = [1;12;48;192;256;512;1024;2048;4096;8192;16384;32768]`;;
let C1089SC_MASKS = [1;12;48;192;256;512;1024;2048;4096;8192;16384;32768];;

let C1089SC_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C1089SC_F = `c1089sc_family`;;
let c1089sc_hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C1089SC_F));;
let c1089sc_np = CONJUNCT1 (ASSUME c1089sc_hyp);;
let c1089sc_inst uth = MP (SPECL C1089SC_VARS uth) (ASSUME c1089sc_hyp);;
let c1089sc_tuple m =
  map (fun f -> list_mk_comb(f, C1089SC_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1089sc_own m x y = list_mk_comb(`linside`, c1089sc_tuple m @ [x; y]);;
let c1089sc_stmt hyps body =
  list_mk_forall(C1089SC_VARS, mk_imp(c1089sc_hyp, itlist (curry mk_imp) hyps body));;
let c1089sc_seed m p = c1089sc_inst (oo_inst C1089SC_F (oo_seed m p));;
let c1089sc_apart m n = c1089sc_inst (oo_apart C1089SC_F m n);;

(* Lean: absent_marker  (marker 1 = (457/500, 1) is in no mask) *)
let C1089SC_ABSENT_MARKER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family
     ==> forall i. i < 12
         ==> ~linside (ooc c1 c2 a b l (EL i c1089sc_masks)) (oos c1 c2 a b l (EL i c1089sc_masks))
                      (oou c1 c2 a b l (EL i c1089sc_masks)) (oov c1 c2 a b l (EL i c1089sc_masks)) l
                      (&457 / &500) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `i < 12 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/
                                      i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[c1089sc_masks] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC(map (fun m -> oo_inst C1089SC_F (oo_missing m 1)) C1089SC_MASKS));;

let c1089sc_absent = c1089sc_inst C1089SC_ABSENT_MARKER;;

let C1089SC_HYPS =
  [c1089sc_own 1 `&91 / &50` `&1`; c1089sc_own 1 `&49 / &25` `&19 / &25`;
   c1089sc_own 512 `&2` `&3 / &2`; c1089sc_own 1024 `&3` `&113 / &50`;
   c1089sc_own 8192 `&12 / &5` `&1`; c1089sc_own 8192 `&14 / &5` `&1`;
   c1089sc_own 16384 `&3` `&8 / &5`];;

(* Lean: original_corner_of_seeds *)
let C1089SC_ORIGINAL_CORNER_OF_SEEDS =
  let ms = [1; 12; 512; 1024; 8192; 16384] in
  let units = map (fun m -> MP (SPECL (C1089SC_VARS @ [mk_small_numeral m]) OO_UNIT) c1089sc_np) ms in
  let boxes = map (fun m -> MP (SPECL (C1089SC_VARS @ [mk_small_numeral m]) OO_BOX) c1089sc_np) ms in
  let side = MP (SPECL C1089SC_VARS OO_SIDE) c1089sc_np in
  let aparts = map (fun (m, n) -> c1089sc_apart m n)
    [16384, 1024; 16384, 512; 12, 16384; 12, 8192; 8192, 512; 8192, 16384; 1, 8192; 1, 12; 8192, 12] in
  let seeds = [c1089sc_seed 1 (`&1`, `&457 / &500`); c1089sc_seed 12 (`&3`, `&457 / &500`);
               c1089sc_seed 12 (`&3`, `&1`); c1089sc_seed 512 (`&47 / &20`, `&33 / &20`);
               c1089sc_seed 8192 (`&2`, `&457 / &500`); c1089sc_seed 16384 (`&1543 / &500`, `&2`)] in
  let facts = units @ boxes @ aparts @ seeds @ map ASSUME C1089SC_HYPS in
  let th = SPECL (List.concat (map c1089sc_tuple ms)) C1089SC_CORNER_OF_SEEDS in
  let corner = MP th (TAC_PROOF(([], lhand (concl th)),
    REPEAT CONJ_TAC THEN
    FIRST [FIRST (map ACCEPT_TAC facts); REFL_TAC;
           MP_TAC side THEN REAL_ARITH_TAC])) in
  prove
   (c1089sc_stmt C1089SC_HYPS (mk_conj(c1089sc_own 1 `&1` `&1`, concl c1089sc_absent)),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT DISCH_TAC THEN
    ACCEPT_TAC (CONJ corner c1089sc_absent));;

(* Lean: original_corner_of_missing_seed_producer *)
let C1089SC_ORIGINAL_CORNER_OF_MISSING_SEED_PRODUCER =
  let near = el 0 C1089SC_HYPS and offrow = el 1 C1089SC_HYPS in
  let corner = c1089sc_own 1 `&1` `&1` in
  let strong = mk_imp(mk_neg corner, mk_conj(near, offrow)) in
  prove
   (c1089sc_stmt (strong :: tl (tl C1089SC_HYPS)) (mk_conj(corner, concl c1089sc_absent)),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC c1089sc_absent] THEN
    ASM_CASES_TAC corner THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = strong)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC (SPEC_ALL C1089SC_ORIGINAL_CORNER_OF_SEEDS) THEN ASM_REWRITE_TAC[]);;
