(* ========================================================================= *)
(* W-F6, part 2b: a faster sound route to PlanarVertexCheck.Check.           *)
(* Lean: Compact/Core/PlanarVertexSparse.lean (Witness = outsideBase /       *)
(*       insideForbidden / targetBounds, Witness.Check, Witness.sound,       *)
(*       PairWitnessCheck(.sound), checkRow(_sound), checkTriangle(_sound),  *)
(*       SparseCheck.toCheck), and a two-row generalisation of               *)
(*       Compact/Core/PlanarBoundaryFilter.lean (LineExclusion: one parallel *)
(*       base row; here: a nonnegative combination of two base rows plus a   *)
(*       multiple of the boundary row is a negative constant, i.e. no point  *)
(*       of the boundary line satisfies the closed base).  Lean's            *)
(*       LineExclusion <i, scale, multiple> is PvLx i i scale 0 (-multiple). *)
(* Untrusted data (n12/scripts/pv_oracle.py): per root the exclusion plan and    *)
(* one witness per unordered pair of the remaining lines.                    *)
(* Result: PVR_WXCHECK_SOUND : pvr_wxcheck w r ins outs plan wits            *)
(*                             ==> pvr_check_at w r ins outs                 *)
(* ========================================================================= *)

needs "n12/cert/PV_Root.ml";;

(* Lean: PlanarVertexSparse.Witness *)
let pvwit_INDUCT,pvwit_RECURSION = define_type "pvwit = PwBase num | PwBlock num | PwTargets";;

(* Lean: Witness.Check *)
let pv_wit_check = define
 `(pv_wit_check (PwBase i) v base forb tgs <=>
     i < LENGTH base /\ pv_veval v (EL i base) < &0) /\
  (pv_wit_check (PwBlock i) v base (forb:(crow list)list) tgs <=>
     i < LENGTH forb /\ ALL (\r. &0 < pv_veval v r) (EL i forb)) /\
  (pv_wit_check PwTargets v base forb tgs <=> ALL (\t. &0 <= pv_veval v t) tgs)`;;

(* Lean: Witness.sound *)
let PV_WIT_SOUND = prove
 (`forall w v base forb tgs. pv_wit_check w v base forb tgs /\ pv_vfeasible v base forb
     ==> ALL (\t. &0 <= pv_veval v t) tgs`,
  MATCH_MP_TAC pvwit_INDUCT THEN REWRITE_TAC[pv_wit_check; pv_vfeasible; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `EL a (base:crow list)`) THEN ASM_SIMP_TAC[MEM_EL] THEN
    ASM_REWRITE_TAC[GSYM INT_NOT_LT];
    FIRST_X_ASSUM(MP_TAC o SPEC `EL a (forb:(crow list)list)`) THEN ASM_SIMP_TAC[MEM_EL]]);;

(* Lean: PairWitnessCheck *)
let pv_pw_check = new_definition
 `pv_pw_check base forb tgs a b w <=>
    pv_det a b = &0 \/ pv_wit_check w (pv_vertex a b) base forb tgs`;;

(* Lean: PairWitnessCheck.sound *)
let PV_PW_SOUND = prove
 (`forall base forb tgs a b w. pv_pw_check base forb tgs a b w ==> pv_pair_check base forb tgs a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_pw_check; pv_pair_check] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PV_WIT_SOUND THEN
  MAP_EVERY EXISTS_TAC [`w:pvwit`; `base:crow list`; `forb:(crow list)list`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: checkRow *)
let pv_check_row = define
 `(pv_check_row base forb tgs (a:crow) [] [] <=> true) /\
  (pv_check_row base forb tgs a [] (CONS (w:pvwit) ws) <=> false) /\
  (pv_check_row base forb tgs a (CONS b bs) [] <=> false) /\
  (pv_check_row base forb tgs a (CONS b bs) (CONS w ws) <=>
     pv_pw_check base forb tgs a b w /\ pv_check_row base forb tgs a bs ws)`;;

(* Lean: checkTriangle *)
let pv_check_tri = define
 `(pv_check_tri base forb tgs [] [] <=> true) /\
  (pv_check_tri base forb tgs [] (CONS (ws:pvwit list) plan) <=> false) /\
  (pv_check_tri base forb tgs (CONS (a:crow) rest) [] <=> false) /\
  (pv_check_tri base forb tgs (CONS a rest) (CONS ws plan) <=>
     pv_check_row base forb tgs a rest ws /\ pv_check_tri base forb tgs rest plan)`;;

(* Lean: checkRow_sound *)
let PV_CHECK_ROW_SOUND = prove
 (`forall base forb tgs a l ws. pv_check_row base forb tgs a l ws
     ==> ALL (pv_pair_check base forb tgs a) l`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ws:pvwit list`,`ws:pvwit list`) THEN
  SPEC_TAC(`l:crow list`,`l:crow list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[pv_check_row; ALL] THEN
  ASM_MESON_TAC[PV_PW_SOUND]);;

(* Lean: checkTriangle_sound *)
let PV_CHECK_TRI_SOUND = prove
 (`forall base forb tgs l plan. pv_check_tri base forb tgs l plan
     ==> pv_triangle (pv_pair_check base forb tgs) l`,
  REPEAT GEN_TAC THEN SPEC_TAC(`plan:(pvwit list)list`,`plan:(pvwit list)list`) THEN
  SPEC_TAC(`l:crow list`,`l:crow list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[pv_check_tri; pv_triangle] THEN
  ASM_MESON_TAC[PV_CHECK_ROW_SOUND]);;

(* ------------------------------------------------------------------------- *)
(* Two-row line exclusion                                                    *)
(* ------------------------------------------------------------------------- *)

let pvlx_INDUCT,pvlx_RECURSION = define_type "pvlx = PvLx num num int int int";;

let pv_lx2_check = define
 `pv_lx2_check (PvLx i j li lj mu) base bnd <=>
    i < LENGTH base /\ j < LENGTH base /\ &0 <= li /\ &0 <= lj /\
    li * cr_x (EL i base) + lj * cr_x (EL j base) + mu * cr_x bnd = &0 /\
    li * cr_y (EL i base) + lj * cr_y (EL j base) + mu * cr_y bnd = &0 /\
    li * cr_c (EL i base) + lj * cr_c (EL j base) + mu * cr_c bnd < &0`;;

let PV_LX2_REAL = prove
 (`forall li lj mu xi yi ci xj yj cj xa ya ca vx vy vd.
     &0 <= li /\ &0 <= lj /\
     li * xi + lj * xj + mu * xa = &0 /\ li * yi + lj * yj + mu * ya = &0 /\
     li * ci + lj * cj + mu * ca < &0 /\ xa * vx + ya * vy + ca * vd = &0 /\ &0 < vd
     ==> xi * vx + yi * vy + ci * vd < &0 \/ xj * vx + yj * vy + cj * vd < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `li * (xi * vx + yi * vy + ci * vd) + lj * (xj * vx + yj * vy + cj * vd) =
                vd * (li * ci + lj * cj + mu * ca)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `vd * (li * ci + lj * cj + mu * ca) < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC PV_MUL_NEG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~(~a /\ ~b) ==> a \/ b`) THEN REWRITE_TAC[REAL_NOT_LT] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`li:real`; `xi * vx + yi * vy + ci * vd`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`lj:real`; `xj * vx + yj * vy + cj * vd`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let PV_LX2_PAIRCHECK = prove
 (`forall h base forb tgs a b. pv_lx2_check h base a ==> pv_pair_check base forb tgs a b`,
  MATCH_MP_TAC pvlx_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `li:int`; `lj:int`; `mu:int`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_lx2_check; pv_pair_check] THEN STRIP_TAC THEN
  ASM_CASES_TAC `pv_det a b = &0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN
  REWRITE_TAC[pv_vfeasible; GSYM ALL_MEM; DE_MORGAN_THM] THEN DISJ1_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; INT_NOT_LE] THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`] PV_DENOMINATOR_POSITIVE) THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`] PV_VERTEX_ON_FIRST) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pv_veval] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `pv_veval (pv_vertex a b) (EL i (base:crow list)) < &0 \/
                pv_veval (pv_vertex a b) (EL j (base:crow list)) < &0` MP_TAC THENL
   [REWRITE_TAC(pv_veval :: INT_REAL_RULES) THEN MATCH_MP_TAC PV_LX2_REAL THEN
    MAP_EVERY EXISTS_TAC [`real_of_int li`; `real_of_int lj`; `real_of_int mu`;
      `real_of_int (cr_x a)`; `real_of_int (cr_y a)`; `real_of_int (cr_c a)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `EL i (base:crow list)`; EXISTS_TAC `EL j (base:crow list)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pv_veval]) THEN ASM_SIMP_TAC[MEM_EL]);;

let pv_filter2 = define
 `(pv_filter2 base [] [] <=> true) /\
  (pv_filter2 base [] (CONS (hh:pvlx option) plan) <=> false) /\
  (pv_filter2 base (CONS (a:crow) rest) [] <=> false) /\
  (pv_filter2 base (CONS a rest) (CONS NONE plan) <=> pv_filter2 base rest plan) /\
  (pv_filter2 base (CONS a rest) (CONS (SOME h) plan) <=>
     pv_lx2_check h base a /\ pv_filter2 base rest plan)`;;

let pv_active2 = define
 `(pv_active2 [] (plan:(pvlx option)list) = []) /\
  (pv_active2 (CONS (a:crow) rest) [] = []) /\
  (pv_active2 (CONS a rest) (CONS NONE plan) = CONS a (pv_active2 rest plan)) /\
  (pv_active2 (CONS a rest) (CONS (SOME h) plan) = pv_active2 rest plan)`;;

let PV_FILTER2_COVER = prove
 (`forall base rws plan. pv_filter2 base rws plan
     ==> forall a. MEM a rws ==> MEM a (pv_active2 rws plan) \/ exists h. pv_lx2_check h base a`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[pv_filter2] THEN
  STRUCT_CASES_TAC (ISPEC `h':pvlx option` (cases "option")) THEN
  REWRITE_TAC[pv_filter2; pv_active2; MEM] THEN ASM_MESON_TAC[]);;

(* the complete fast check *)
let pv_wcheck = new_definition
 `pv_wcheck base forb tgs plan wits <=>
    pv_filter2 base (APPEND base (lflat forb)) plan /\
    pv_check_tri base forb tgs (pv_active2 (APPEND base (lflat forb)) plan) wits`;;

let PV_WCHECK_CHECK = prove
 (`forall base forb tgs plan wits. pv_wcheck base forb tgs plan wits ==> pv_check base forb tgs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_wcheck; pv_check] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PV_FILTER2_COVER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PV_CHECK_TRI_SOUND) THEN
  MP_TAC(ISPECL [`pv_pair_check base forb tgs`; `pv_active2 (APPEND base (lflat forb)) plan`]
    PV_TRIANGLE_ALL) THEN
  ASM_REWRITE_TAC[PV_PAIR_REFL] THEN ANTS_TAC THENL [MATCH_ACCEPT_TAC PV_PAIR_SWAP; ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:crow`; `b:crow`] THEN STRIP_TAC THEN
  ASM_MESON_TAC[PV_LX2_PAIRCHECK; PV_PAIR_SWAP]);;

(* ------------------------------------------------------------------------- *)
(* Executable forms                                                          *)
(* ------------------------------------------------------------------------- *)

let pv_wit_x = define
 `(pv_wit_x (PwBase i) v base forb tgs <=>
     if i < LENGTH base then pv_veval v (EL i base) < &0 else false) /\
  (pv_wit_x (PwBlock i) v base (forb:(crow list)list) tgs <=>
     if i < LENGTH forb then pv_blk_pos v (EL i forb) else false) /\
  (pv_wit_x PwTargets v (base:crow list) (forb:(crow list)list) tgs <=> pv_base_ok v tgs)`;;

let PV_WIT_X = prove
 (`forall w v base forb tgs. pv_wit_x w v base forb tgs <=> pv_wit_check w v base forb tgs`,
  MATCH_MP_TAC pvwit_INDUCT THEN
  REWRITE_TAC[pv_wit_x; pv_wit_check; PV_BLK_POS; PV_BASE_OK] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let pv_wpc = new_definition
 `pv_wpc base forb tgs a b w <=>
    let d = pv_det a b in if d = &0 then true else pv_wit_x w (pv_vtx a b d) base forb tgs`;;

let PV_WPC = prove
 (`forall base forb tgs a b w. pv_wpc base forb tgs a b w <=> pv_pw_check base forb tgs a b w`,
  REWRITE_TAC[pv_wpc; pv_pw_check; LET_DEF; LET_END_DEF; PV_VTX; PV_WIT_X] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let pv_xrow = define
 `(pv_xrow base forb tgs (a:crow) [] [] <=> true) /\
  (pv_xrow base forb tgs a [] (CONS (w:pvwit) ws) <=> false) /\
  (pv_xrow base forb tgs a (CONS b bs) [] <=> false) /\
  (pv_xrow base forb tgs a (CONS b bs) (CONS w ws) <=>
     if pv_wpc base forb tgs a b w then pv_xrow base forb tgs a bs ws else false)`;;

let pv_xtri = define
 `(pv_xtri base forb tgs [] [] <=> true) /\
  (pv_xtri base forb tgs [] (CONS (ws:pvwit list) plan) <=> false) /\
  (pv_xtri base forb tgs (CONS (a:crow) rest) [] <=> false) /\
  (pv_xtri base forb tgs (CONS a rest) (CONS ws plan) <=>
     if pv_xrow base forb tgs a rest ws then pv_xtri base forb tgs rest plan else false)`;;

let PV_XROW = prove
 (`forall base forb tgs a l ws. pv_xrow base forb tgs a l ws <=> pv_check_row base forb tgs a l ws`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ws:pvwit list`,`ws:pvwit list`) THEN
  SPEC_TAC(`l:crow list`,`l:crow list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_xrow; pv_check_row; PV_WPC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let PV_XTRI = prove
 (`forall base forb tgs l plan. pv_xtri base forb tgs l plan <=> pv_check_tri base forb tgs l plan`,
  REPEAT GEN_TAC THEN SPEC_TAC(`plan:(pvwit list)list`,`plan:(pvwit list)list`) THEN
  SPEC_TAC(`l:crow list`,`l:crow list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_xtri; pv_check_tri; PV_XROW] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let pv_wfast = new_definition
 `pv_wfast base forb tgs plan wits <=>
    let L = APPEND base (lflat forb) in
    if pv_filter2 base L plan then pv_xtri base forb tgs (pv_active2 L plan) wits else false`;;

let PV_WFAST = prove
 (`forall base forb tgs plan wits. pv_wfast base forb tgs plan wits ==> pv_check base forb tgs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_wfast; LET_DEF; LET_END_DEF; PV_XTRI] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC PV_WCHECK_CHECK THEN
  MAP_EVERY EXISTS_TAC [`plan:(pvlx option)list`; `wits:(pvwit list)list`] THEN
  ASM_REWRITE_TAC[pv_wcheck]);;

(* executable root check with the fast vertex route (the root's own Lean plan is not used) *)
let pvr_wxcheck = define
 `pvr_wxcheck w (PvRoot a base forb res plan0) ins outs plan wits <=>
    if pv_box (MAP FST base) then
      if pv_wfast (MAP FST base) (MAP (MAP FST) forb) (pv_target_rows res) plan wits then
        pv_strict_ok res /\ pv_res_angle a res /\
        (let ii = pv_inputs w ins in ALL (\rd. 0 < SND rd /\ MEM (pv_decode rd) ii) base) /\
        (let ff = pv_forbidden w outs in
         ALL (\blk. ALL (\rd. 0 < SND rd) blk /\ MEM (MAP pv_decode blk) ff) forb)
      else false
    else false`;;

let PVR_WXCHECK_SOUND = prove
 (`forall w r ins outs plan wits. pvr_wxcheck w r ins outs plan wits ==> pvr_check_at w r ins outs`,
  GEN_TAC THEN MATCH_MP_TAC pvroot_INDUCT THEN
  REWRITE_TAC[pvr_wxcheck; pvr_check_at; pv_forms_ok; pv_blocks_ok; PV_INPUTS; PV_FORBIDDEN;
              LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PV_WFAST]);;
