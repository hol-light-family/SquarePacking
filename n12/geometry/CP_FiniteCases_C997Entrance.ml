(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C997Entrance.lean.                *)
(* The compulsory C997 wall and merged-corner points.                       *)
(* Lean  G p mask = natAuxOwners p 1 (ownerIndex p mask)  is  c997e_G.      *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_FiniteCases_MergedCornerPoint.ml";;

(* Lean: family *)
let c997e_family = new_definition
 `c997e_family = {1,2,12,48,256,512,1024,2240,4096,8192,16384,32768}`;;
let C997E_F = `c997e_family`;;

(* Lean: swDomain, lowDomain, centralDomain, wallDomain (private, ofSingle) *)
let C997E_SW = ro_single C997E_F 3;;
let C997E_LOW = ro_single C997E_F 7;;
let C997E_CENTRAL = ro_single C997E_F 23;;
let C997E_WALL = ro_single C997E_F 58;;

(* Lean: G *)
let c997e_G = new_definition
 `c997e_G (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    auxown 1 (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
             (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l`;;

(* Lean: actual (private) *)
let C997E_ACTUAL = prove
 (`forall c1 c2 a b l m al. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family /\
     m IN c997e_family /\ hdom c997e_family m 1 al ==> MEM (c997e_G c1 c2 a b l m) al`,
  REWRITE_TAC[c997e_G] THEN MESON_TAC[HDOM_OWNER]);;

(* Lean: separate (private) *)
let C997E_SEPARATE = prove
 (`forall c1 c2 a b l m n. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family /\
     m IN c997e_family /\ n IN c997e_family /\ ~(m = n)
     ==> DISJOINT (c997e_G c1 c2 a b l m) (c997e_G c1 c2 a b l n)`,
  REWRITE_TAC[c997e_G] THEN MESON_TAC[OO_AUXK_DISJOINT]);;

(* Lean: wall_label *)
let C997E_WALL_LABEL =
  let th = pk_forced_half 1 C997E_F [C997E_SW; C997E_LOW; C997E_CENTRAL; C997E_WALL] 4096 `{1}` in
  prove(`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family
           ==> c997e_G c1 c2 a b l 4096 = {1}`,
    REWRITE_TAC[c997e_G; th]);;

(* Lean: seed_point (private) is oo_seed *)
let c997e_seed m (x, y) = oo_inst C997E_F (oo_seed m (x, y));;

let c997e_own m x y = list_mk_comb(`linside`,
  map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                                 mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; x; y]);;
let c997e_stmt concl = mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`,
  mk_forall(`b:num->real`, mk_forall(`l:real`,
    mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family`, concl))))));;

(* Lean: wall_upper *)
let C997E_WALL_UPPER = prove
 (c997e_stmt (c997e_own 4096 `&1` `&12 / &5`),
  REPEAT STRIP_TAC THEN REWRITE_TAC[oo_auxk_point 1 1] THEN
  MP_TAC (SPEC_ALL C997E_WALL_LABEL) THEN ASM_REWRITE_TAC[c997e_G] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_INSERT]);;

let C997E_CLOSE_TAC ths =
  REPEAT CONJ_TAC THEN
  FIRST [ASM_SIMP_TAC (ths @ [OO_UNIT; OO_BOX; OO_SIDE]) THEN NO_TAC;
         MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];;

(* Lean: wall_far *)
let C997E_WALL_FAR = prove
 (c997e_stmt (c997e_own 4096 `&1` `&14 / &5`),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C981WA_POINT THEN
  C997E_CLOSE_TAC
   [c997e_seed 4096 (`&457 / &500`, `&2`); C997E_WALL_UPPER;
    oo_excl C997E_F 4096 2 (c997e_seed 2 (`&1`, `&87 / &50`));
    oo_excl C997E_F 4096 2 (c997e_seed 2 (`&19 / &25`, `&187 / &100`));
    oo_excl C997E_F 4096 2240 (c997e_seed 2240 (`&33 / &20`, `&47 / &20`))]);;

(* Lean: merged_near *)
let C997E_MERGED_NEAR = prove
 (c997e_stmt (c997e_own 2240 `&1` `&1457 / &500`),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FCMCP_UPPER_LEFT THEN
  C997E_CLOSE_TAC
   [c997e_seed 2240 (`&457 / &500`, `&3`); c997e_seed 2240 (`&1`, `&1543 / &500`);
    c997e_seed 2240 (`&33 / &20`, `&47 / &20`);
    oo_excl C997E_F 2240 32768 (c997e_seed 32768 (`&2`, `&1543 / &500`))]);;

(* Lean: merged_outward (fourDatum4 on pullY of the owner: points mirrored in y) *)
let C997E_FOUR = oo_four_point ((`&457 / &500`, `&3`), (`&33 / &20`, `&47 / &20`),
                                (`&1`, `&12 / &5`), (`&8 / &5`, `&3`));;
let C997E_MERGED_OUTWARD = prove
 (c997e_stmt (c997e_own 2240 `&8 / &5` `&3`),
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC_ALL (oo_excl C997E_F 2240 4096 C997E_WALL_UPPER)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `2240`] C997E_FOUR) THEN
  ASM_SIMP_TAC[c997e_seed 2240 (`&457 / &500`, `&3`); c997e_seed 2240 (`&33 / &20`, `&47 / &20`)]);;
