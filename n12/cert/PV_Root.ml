(* ========================================================================= *)
(* W-F6, part 2: initial-cover roots and owners.                             *)
(* Lean: Compact/Bridge/DirectPoseCover.lean (Form, Form.decode, StrictOK,   *)
(*       holds_of_nonnegative, holds_of_positive, Root, baseRows,            *)
(*       forbiddenRows, targetRows, strictOK, Root.Check, Root.leaves,       *)
(*       Root.sound, Owner, Owner.Check, Owner.leaves, Owner.oriented_sound),*)
(*       Compact/Bridge/DirectPoseForms.lean (sourceRoot: base forms are     *)
(*       encoded poseInputs rows, forbidden = all of poseForbidden),         *)
(*       Compact/Bridge/DirectRecipeTable.lean (Spec: angle index, target    *)
(*       pose of the dictionary with the same angle; checkedOwner_leaves),   *)
(*       Compact/Bridge/DirectCachedRecipe.lean (the boundary filter cache). *)
(* HOL root  PvRoot a base forb res plan:                                    *)
(*   a     : angle index (s12_angles a, Lean bank.angles spec.angle)          *)
(*   base  : (crow # den) list   (Lean base : List Form, den = denPred + 1)   *)
(*   forb  : (crow # den) list list                                          *)
(*   res   : cpose option        (Lean spec.target; result rows = cp_rows)   *)
(*   plan  : line-exclusion plan (Lean PlanarBoundaryHints.Cache.plan)       *)
(* The leaves of a root are dictionary poses (cr_leaf), so the owner cover   *)
(* is stated directly on MAP cr_leaf <domain constant> (design §4.3).        *)
(* ========================================================================= *)

needs "n12/cert/PV_Vertex.ml";;

let pvroot_INDUCT,pvroot_RECURSION = define_type
  "pvroot = PvRoot num ((crow#num)list) (((crow#num)list)list) (cpose option)
                   (((num#int#int)option)list)";;

let pvr_angle = define `pvr_angle (PvRoot a b f r p) = a`;;
let pvr_base = define `pvr_base (PvRoot a b f r p) = b`;;
let pvr_forb = define `pvr_forb (PvRoot a b f r p) = f`;;
let pvr_result = define `pvr_result (PvRoot a b f r p) = r`;;
let pvr_plan = define `pvr_plan (PvRoot a b f r p) = p`;;

(* Lean: Form.decode *)
let pv_decode = new_definition `pv_decode (rd:crow#num) = cr_normalized (FST rd) (SND rd)`;;

(* Lean: Root.targetRows *)
let pv_target_rows = define
 `(pv_target_rows NONE = [CRow (&0) (&0) (-- &1) false]) /\
  (pv_target_rows (SOME p) = cp_rows p)`;;

(* Lean: Form.StrictOK, Root.strictOK *)
let pv_strict_ok = define
 `(pv_strict_ok NONE <=> true) /\
  (pv_strict_ok (SOME p) <=>
     ALL (\r. ~cr_s r \/ (cr_x r = &0 /\ cr_y r = &0 /\ &0 < cr_c r)) (cp_rows p))`;;

(* Lean: Spec.Check, target part (spec.angle = bank.poseAngle target) *)
let pv_res_angle = define
 `(pv_res_angle a NONE <=> true) /\ (pv_res_angle a (SOME p) <=> cp_angle p = a)`;;

(* Lean: Root.leaves (as dictionary poses; cr_leaf gives the PoseLeaf) *)
let pv_leaves = define `(pv_leaves NONE = []) /\ (pv_leaves (SOME (p:cpose)) = [p])`;;

(* Lean: Root.Check, the membership conjuncts
   (forall f in base, decode f in poseInputs angle inside;
    forall block in forbidden, map decode block in poseForbidden angle outside) *)
let pv_forms_ok = new_definition
 `pv_forms_ok w ins base <=>
    ALL (\rd. 0 < SND rd /\ MEM (pv_decode rd) (pose_inputs w ins)) base`;;
let pv_blocks_ok = new_definition
 `pv_blocks_ok w outs forb <=>
    ALL (\blk. ALL (\rd. 0 < SND rd) blk /\ MEM (MAP pv_decode blk) (pose_forbidden w outs)) forb`;;

(* Lean: Root.Check (with the angle w = s12_angles a supplied explicitly) *)
let pvr_check_at = define
 `pvr_check_at w (PvRoot a base forb res plan) ins outs <=>
    pv_box (MAP FST base) /\
    pv_check (MAP FST base) (MAP (MAP FST) forb) (pv_target_rows res) /\
    pv_forms_ok w ins base /\ pv_blocks_ok w outs forb /\
    pv_strict_ok res /\ pv_res_angle a res`;;

(* the root check with Lean's angle subtype (index < 192, angles = s12_angles) *)
let pvr_check = new_definition
 `pvr_check r ins outs <=> pvr_angle r < 192 /\ pvr_check_at (s12_angles (pvr_angle r)) r ins outs`;;

let PVR_CHECK_INTRO = prove
 (`forall a base forb res plan w ins outs.
     a < 192 /\ s12_angles a = w /\ pvr_check_at w (PvRoot a base forb res plan) ins outs
     ==> pvr_check (PvRoot a base forb res plan) ins outs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[pvr_check; pvr_angle]);;

(* ------------------------------------------------------------------------- *)
(* Explicit forms of poseInputs / poseForbidden (for evaluation).            *)
(* ------------------------------------------------------------------------- *)

let pv_point_rows = define
 `pv_point_rows (RefSq c s side) (px:real, py:real) =
    [LinCon (Affine [--c; --s] (side / &2 + c * px + s * py)) true;
     LinCon (Affine [c; s] (side / &2 - c * px - s * py)) true;
     LinCon (Affine [s; --c] (side / &2 - s * px + c * py)) true;
     LinCon (Affine [--s; c] (side / &2 + s * px - c * py)) true]`;;

let pv_wall_rows = new_definition
 `pv_wall_rows wl =
    [LinCon (Affine [&1; &0] (--(wl / &2))) false; LinCon (Affine [-- &1; &0] (&4 - wl / &2)) false;
     LinCon (Affine [&0; &1] (--(wl / &2))) false; LinCon (Affine [&0; -- &1] (&4 - wl / &2)) false]`;;

let pv_inputs = new_definition
 `pv_inputs w ins =
    APPEND (APPEND (lflat (MAP (pv_point_rows (outer_ref w)) ins)) (pv_wall_rows (ae_wall w)))
           [LinCon (Affine [&0; &0] (&1)) true]`;;

let pv_forbidden = new_definition
 `pv_forbidden w outs = MAP (pv_point_rows (ae_reference w (&1))) outs`;;

let PV_AFF2 = prove
 (`(forall a. aff_const 2 a = Affine [&0; &0] a) /\
   aff_coord 2 0 = Affine [&1; &0] (&0) /\ aff_coord 2 1 = Affine [&0; &1] (&0)`,
  REWRITE_TAC[aff_const; aff_coord; ARITH_RULE `2 = SUC 1 /\ 1 = SUC 0`; REPLICATE; lunitv;
              NOT_SUC; SUC_SUB1]);;

let PV_POINT_ROWS = prove
 (`point_forms = pv_point_rows`,
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:refsq` THEN X_GEN_TAC `P:real#real` THEN
  MP_TAC(ISPEC `r:refsq` (cases "refsq")) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `P:real#real` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[point_forms; inside_forms; pv_point_rows; rs_c; rs_s; rs_side; PV_AFF2;
                  aff_sub; aff_add; aff_scale; MAP; ladd; CONS_11; injectivity "lincon";
                  injectivity "affine"; FST; SND] THEN
  REAL_ARITH_TAC);;

let PV_WALL_ROWS = prove
 (`forall w. wall_forms w = pv_wall_rows (ae_wall w)`,
  REWRITE_TAC[wall_forms; pv_wall_rows; PV_AFF2; aff_sub; aff_add; aff_scale; MAP; ladd; CONS_11;
              injectivity "lincon"; injectivity "affine"] THEN REAL_ARITH_TAC);;

let PV_INPUTS = prove
 (`forall w ins. pose_inputs w ins = pv_inputs w ins`,
  REWRITE_TAC[pose_inputs; pv_inputs; PV_POINT_ROWS; PV_WALL_ROWS; PV_AFF2]);;

let PV_FORBIDDEN = prove
 (`forall w outs. pose_forbidden w outs = pv_forbidden w outs`,
  REWRITE_TAC[pose_forbidden; pv_forbidden; PV_POINT_ROWS]);;

(* executable root check (Lean: the cached Entry.Check / LiteralCheck route) *)
let pvr_xcheck = define
 `pvr_xcheck w (PvRoot a base forb res plan) ins outs <=>
    if pv_box (MAP FST base) then
      if pv_fast (MAP FST base) (MAP (MAP FST) forb) (pv_target_rows res) plan then
        pv_strict_ok res /\ pv_res_angle a res /\
        (let ii = pv_inputs w ins in ALL (\rd. 0 < SND rd /\ MEM (pv_decode rd) ii) base) /\
        (let ff = pv_forbidden w outs in
         ALL (\blk. ALL (\rd. 0 < SND rd) blk /\ MEM (MAP pv_decode blk) ff) forb)
      else false
    else false`;;

let PVR_XCHECK_SOUND = prove
 (`forall w r ins outs. pvr_xcheck w r ins outs ==> pvr_check_at w r ins outs`,
  GEN_TAC THEN MATCH_MP_TAC pvroot_INDUCT THEN
  REWRITE_TAC[pvr_xcheck; pvr_check_at; pv_forms_ok; pv_blocks_ok; PV_INPUTS; PV_FORBIDDEN;
              LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PV_FAST; PV_FCHECK_CHECK]);;

(* ------------------------------------------------------------------------- *)
(* Soundness                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Lean: Form.holds_of_positive (integer rw) *)
let CR_HOLDS_OF_POS = prove
 (`forall r px py. &0 < cr_eval r px py ==> cr_holds r px py`,
  REWRITE_TAC[cr_holds] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Lean: Form.holds_of_nonnegative *)
let PV_HOLDS_OF_NONNEG = prove
 (`forall r px py. (~cr_s r \/ (cr_x r = &0 /\ cr_y r = &0 /\ &0 < cr_c r)) /\ &0 <= cr_eval r px py
     ==> cr_holds r px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cr_holds] THEN
  ASM_CASES_TAC `cr_s r` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cr_eval] THEN STRIP_TAC THEN ASM_REWRITE_TAC INT_REAL_RULES THEN
  RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN ASM_REAL_ARITH_TAC);;

(* Lean: Root.sound *)
let PV_ROOT_SOUND = prove
 (`forall r ins outs c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ pvr_check r ins outs /\
     c = normalC t /\ s = normalS t /\
     ae_lower (s12_angles (pvr_angle r)) <= t /\ t <= ae_upper (s12_angles (pvr_angle r)) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)) /\
     (forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P))
     ==> exists p. pvr_result r = SOME p /\ cp_angle p = pvr_angle r /\
             forall rw. MEM rw (cp_rows p) ==> cr_holds rw (lcx c s u v a) (lcy c s u v a)`,
  MATCH_MP_TAC pvroot_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`ang:num`; `base:(crow#num)list`; `forb:((crow#num)list)list`;
                       `res:cpose option`; `plan:((num#int#int)option)list`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pvr_check; pvr_check_at; pvr_angle; pvr_result; pv_forms_ok; pv_blocks_ok;
              GSYM ALL_MEM] THEN
  STRIP_TAC THEN
  ABBREV_TAC `w = s12_angles ang` THEN
  SUBGOAL_THEN `ae_check w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC S12_ANGLES_CHECKED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`w:angle_enc`; `ins:(real#real)list`; `c:real`; `s:real`; `u:real`; `v:real`;
                `a:real`; `t:real`] PR_POSEINPUTS_SOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`w:angle_enc`; `outs:(real#real)list`; `c:real`; `s:real`; `u:real`; `v:real`;
                `a:real`; `t:real`] PR_POSEFORBIDDEN_SOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
     (rand (concl th) = `normalC t` || rand (concl th) = `normalS t`)))) THEN
  SUBGOAL_THEN `pv_feasible (MAP FST (base:(crow#num)list)) (MAP (MAP FST) (forb:((crow#num)list)list))
                 (lcx c s u v a) (lcy c s u v a)`
    ASSUME_TAC THENL
   [REWRITE_TAC[pv_feasible; MEM_MAP] THEN CONJ_TAC THENL
     [X_GEN_TAC `rw:crow` THEN DISCH_THEN(X_CHOOSE_THEN `rd:crow#num` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC CR_HOLDS_NONNEG THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `rd:crow#num` o check (fun th ->
        can (find_term ((=) `pv_decode`)) (concl th) && can (find_term ((=) `pose_inputs`)) (concl th))) THEN
      ASM_REWRITE_TAC[pv_decode] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `cr_normalized (FST(rd:crow#num)) (SND rd)` o check (fun th ->
        can (find_term ((=) `lc_holds`)) (concl th) && can (find_term ((=) `pose_inputs`)) (concl th))) THEN
      ASM_SIMP_TAC[CR_NORMALIZED_HOLDS_IFF];
      X_GEN_TAC `blk:crow list` THEN
      DISCH_THEN(X_CHOOSE_THEN `bd:(crow#num)list` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `bd:(crow#num)list` o check (fun th ->
        can (find_term ((=) `pv_decode`)) (concl th) && can (find_term ((=) `pose_forbidden`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `MAP pv_decode bd` o check (fun th ->
        can (find_term ((=) `lc_holds`)) (concl th) && can (find_term ((=) `pose_forbidden`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MEM_MAP; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`f:lincon`; `rd:crow#num`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      REWRITE_TAC[pv_decode] THEN
      SUBGOAL_THEN `0 < SND(rd:crow#num)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[CR_NORMALIZED_HOLDS_IFF] THEN MATCH_MP_TAC CR_HOLDS_OF_POS THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `FST:crow#num->crow`)) (concl th) &&
                                                    is_forall (concl th) &&
                                                    can (find_term ((=) `(<):real->real->bool`)) (concl th))) THEN
      REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `rd:crow#num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP FST (base:(crow#num)list)`; `MAP (MAP FST) (forb:((crow#num)list)list)`;
                `pv_target_rows res`; `lcx c s u v a`; `lcy c s u v a`] PV_CHECK_SOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `res:cpose option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `p:cpose` SUBST_ALL_TAC)) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `CRow (&0) (&0) (-- &1) false`) THEN
    REWRITE_TAC([pv_target_rows; MEM; cr_eval; cr_x; cr_y; cr_c] @ INT_REAL_RULES) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `p:cpose` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pv_target_rows; pv_strict_ok; pv_res_angle; GSYM ALL_MEM]) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `rw:crow` THEN DISCH_TAC THEN
  MATCH_MP_TAC PV_HOLDS_OF_NONNEG THEN ASM_SIMP_TAC[]);;

(* Lean: Owner.oriented_sound, with Owner.Check = CoversInterval 0 1 of the
   root angles and the roots' checks, and Owner.leaves = flatMap Root.leaves *)
let PV_OWNER_SOUND = prove
 (`forall roots ins outs c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     covers_interval (&0) (&1) (MAP (\r. s12_angles (pvr_angle r)) roots) /\
     (forall r. MEM r roots ==> pvr_check r ins outs) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)) /\
     (forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P))
     ==> oriented_pose_covered (MAP cr_leaf (lflat (MAP (\r. pv_leaves (pvr_result r)) roots)))
                               c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`s':real`; `c':real`] AE_FIRST_QUADRANT_RATIONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[GSYM normalS])
                     (ASSUME_TAC o REWRITE_RULE[GSYM normalC]))))) THEN
  MP_TAC(SPECL [`MAP (\r. s12_angles (pvr_angle r)) roots`; `&0`; `&1`; `t:real`]
    IC_COVERSINTERVAL_SOUND) THEN
  ASM_REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `ang:angle_enc` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `root:pvroot` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `ang = s12_angles (pvr_angle root)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `pvr_check root ins outs` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`root:pvroot`; `ins:(real#real)list`; `outs:(real#real)list`; `c':real`; `s':real`;
                `u':real`; `v':real`; `a':real`; `t:real`] PV_ROOT_SOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:cpose` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[oriented_pose_covered] THEN EXISTS_TAC `cr_leaf p` THEN CONJ_TAC THENL
   [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `p:cpose` THEN REWRITE_TAC[MEM_LFLAT; MEM_MAP] THEN
    EXISTS_TAC `pv_leaves (pvr_result root)` THEN CONJ_TAC THENL
     [EXISTS_TAC `root:pvroot` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[pv_leaves; MEM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_angle (cr_leaf p) = s12_angles (pvr_angle root)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[cr_leaf; pl_angle_th]; ALL_TAC] THEN
  REWRITE_TAC[oriented_realizes; pose_realizes; angle_witness; CR_CENTRE_HOLDS] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    X_GEN_TAC `P:real#real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`s12_angles (pvr_angle root)`; `&1`; `c':real`; `s':real`; `u':real`; `v':real`;
                  `a':real`; `t:real`] AR_INNER_SOUND) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `pvr_check root ins outs` THEN REWRITE_TAC[pvr_check] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[S12_ANGLES_CHECKED] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `P:real#real`) THEN ASM_REWRITE_TAC[IN_SQSET];
    MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `t:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* the per-owner checks as one recursive predicate (built by CONJ) *)
let pv_all_check = define
 `(pv_all_check ins outs [] <=> true) /\
  (pv_all_check ins outs (CONS r rs) <=> pvr_check r ins outs /\ pv_all_check ins outs rs)`;;

let PV_ALL_CHECK = prove
 (`forall ins outs roots. pv_all_check ins outs roots <=> forall r. MEM r roots ==> pvr_check r ins outs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_all_check; MEM] THEN
  MESON_TAC[]);;

(* Lean: Owner.oriented_sound for checkedOwner (all roots checked, angle cover) *)
let PV_OWNER_THM = prove
 (`forall roots ins outs.
     covers_interval (&0) (&1) (MAP (\r. s12_angles (pvr_angle r)) roots) /\
     pv_all_check ins outs roots
     ==> forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
                     lcont c s u v a /\
                     (forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)) /\
                     (forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P))
                     ==> oriented_pose_covered
                           (MAP cr_leaf (lflat (MAP (\r. pv_leaves (pvr_result r)) roots))) c s u v a`,
  REWRITE_TAC[PV_ALL_CHECK] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC PV_OWNER_SOUND THEN
  MAP_EVERY EXISTS_TAC [`ins:(real#real)list`; `outs:(real#real)list`] THEN ASM_REWRITE_TAC[]);;

(* the same with the flattened leaf list named (the domain constant) *)
let PV_OWNER_THM_D = prove
 (`forall roots ins outs D.
     covers_interval (&0) (&1) (MAP (\r. s12_angles (pvr_angle r)) roots) /\
     pv_all_check ins outs roots /\
     lflat (MAP (\r. pv_leaves (pvr_result r)) roots) = D
     ==> forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
                     lcont c s u v a /\
                     (forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)) /\
                     (forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P))
                     ==> oriented_pose_covered (MAP cr_leaf D) c s u v a`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (SUBST1_TAC o SYM))) THEN
  MATCH_MP_TAC PV_OWNER_THM THEN ASM_REWRITE_TAC[]);;

(* spine lemmas for the owner assembly (structural, linear in the number of roots) *)
let PV_MAP_ANGLE_CONS = prove
 (`(MAP (\r. s12_angles (pvr_angle r)) [] = []) /\
   (forall a b f re p t. MAP (\r. s12_angles (pvr_angle r)) (CONS (PvRoot a b f re p) t) =
                   CONS (s12_angles a) (MAP (\r. s12_angles (pvr_angle r)) t))`,
  REWRITE_TAC[MAP; pvr_angle]);;

let PV_FLAT_CONS = prove
 (`(lflat (MAP (\r. pv_leaves (pvr_result r)) []) = []) /\
   (forall a b f q p t. lflat (MAP (\r. pv_leaves (pvr_result r)) (CONS (PvRoot a b f (SOME q) p) t)) =
                  CONS q (lflat (MAP (\r. pv_leaves (pvr_result r)) t))) /\
   (forall a b f p t. lflat (MAP (\r. pv_leaves (pvr_result r)) (CONS (PvRoot a b f NONE p) t)) =
                lflat (MAP (\r. pv_leaves (pvr_result r)) t))`,
  REWRITE_TAC[MAP; pvr_result; pv_leaves; lflat; APPEND]);;
