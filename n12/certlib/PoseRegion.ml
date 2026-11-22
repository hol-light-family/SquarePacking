(* ========================================================================= *)
(* Port of source/S12/PoseRegion.lean (Jatloe, N12-jatloe).                  *)
(* Rows are LinearConstraint 2 = lincon evaluated at [centerX q; centerY q] *)
(* = [lcx c s u v a; lcy c s u v a].  A PoseRoot <angle, tree> is            *)
(* PoseRoot angle tree; the subtype check of angle is part of proot_check.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/PoseBounds.ml";;
needs "n12/certlib/AffineOverlap.ml";;
needs "n12/certlib/RegionTree.ml";;

(* Lean: outerReference *)
let outer_ref = new_definition
 `outer_ref w = RefSq (ae_c w) (ae_s w) ((&1001 / &1000) * ae_outer w)`;;

(* Lean: pointForms *)
let point_forms = new_definition
 `point_forms r (P:real#real) =
    inside_forms 2 r (aff_coord 2 0) (aff_coord 2 1) (aff_const 2 (FST P)) (aff_const 2 (SND P))`;;

(* Lean: wallForms *)
let wall_forms = new_definition
 `wall_forms w =
    [LinCon (aff_sub (aff_coord 2 0) (aff_const 2 (ae_wall w / &2))) false;
     LinCon (aff_sub (aff_const 2 (&4 - ae_wall w / &2)) (aff_coord 2 0)) false;
     LinCon (aff_sub (aff_coord 2 1) (aff_const 2 (ae_wall w / &2))) false;
     LinCon (aff_sub (aff_const 2 (&4 - ae_wall w / &2)) (aff_coord 2 1)) false]`;;

(* Lean: poseInputs *)
let pose_inputs = new_definition
 `pose_inputs w inside =
    APPEND (APPEND (lflat (MAP (point_forms (outer_ref w)) inside)) (wall_forms w))
           [LinCon (aff_const 2 (&1)) true]`;;

(* Lean: poseForbidden *)
let pose_forbidden = new_definition
 `pose_forbidden w outside = MAP (point_forms (ae_reference w (&1))) outside`;;

let PR_COORD2 = prove
 (`forall x y. aff_eval (aff_coord 2 0) [x; y] = x /\ aff_eval (aff_coord 2 1) [x; y] = y`,
  SIMP_TAC[AO_AFF_EVAL_COORD; LENGTH; ARITH] THEN REWRITE_TAC[ONE; EL; HD; TL]);;

let PR_POINT_FORMS_IFF = prove
 (`forall r P x y.
     (forall f. MEM f (point_forms r P) ==> lc_holds f [x; y]) <=>
     abs(rs_c r * (FST P - x) + rs_s r * (SND P - y)) < rs_side r / &2 /\
     abs(--(rs_s r) * (FST P - x) + rs_c r * (SND P - y)) < rs_side r / &2`,
  REWRITE_TAC[point_forms; AO_INSIDE_FORMS_IFF; PR_COORD2; AO_AFF_EVAL_CONST]);;

(* Lean: poseInputs_sound *)
let PR_POSEINPUTS_SOUND = prove
 (`forall w inside c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     ae_check w /\ c = normalC t /\ s = normalS t /\
     ae_lower w <= t /\ t <= ae_upper w /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P inside ==> linside c s u v a (FST P) (SND P))
     ==> forall f. MEM f (pose_inputs w inside) ==> lc_holds f [lcx c s u v a; lcy c s u v a]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PB_FLIP_NORMAL_TAC THEN
  REWRITE_TAC[pose_inputs; MEM_APPEND; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MEM_LFLAT; MEM_MAP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f:lincon` THEN X_GEN_TAC `l:lincon list` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `P:real#real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    UNDISCH_TAC `MEM (f:lincon) l` THEN ASM_REWRITE_TAC[] THEN SPEC_TAC(`f:lincon`,`f:lincon`) THEN
    REWRITE_TAC[PR_POINT_FORMS_IFF; outer_ref; rs_c; rs_s; rs_side] THEN
    MP_TAC(SPECL [`w:angle_enc`; `&1001 / &1000`; `c:real`; `s:real`; `u:real`; `v:real`;
                  `a:real`; `t:real`; `FST(P:real#real)`; `SND(P:real#real)`] PB_OUTER_SOUND) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`w:angle_enc`; `&1`; `c:real`; `s:real`; `u:real`; `v:real`;
                  `a:real`; `t:real`] PB_WALL_SOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[wall_forms; MEM; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[lc_holds; AO_AFF_EVAL_SUB; PR_COORD2; AO_AFF_EVAL_CONST] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[MEM; FORALL_UNWIND_THM2; lc_holds; AO_AFF_EVAL_CONST] THEN REAL_ARITH_TAC]);;

(* Lean: poseForbidden_sound *)
let PR_POSEFORBIDDEN_SOUND = prove
 (`forall w outside c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     ae_check w /\ c = normalC t /\ s = normalS t /\
     ae_lower w <= t /\ t <= ae_upper w /\ &1 < a /\
     (forall P. MEM P outside ==> ~linside c s u v a (FST P) (SND P))
     ==> forall block. MEM block (pose_forbidden w outside)
                 ==> ~(forall f. MEM f block ==> lc_holds f [lcx c s u v a; lcy c s u v a])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PB_FLIP_NORMAL_TAC THEN
  REWRITE_TAC[pose_forbidden; MEM_MAP; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `block:lincon list` THEN X_GEN_TAC `P:real#real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:real#real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`w:angle_enc`; `&1`; `c:real`; `s:real`; `u:real`; `v:real`;
                `a:real`; `t:real`] AR_INNER_SOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `P:real#real`) THEN REWRITE_TAC[IN_SQSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPECL [`2`; `ae_reference w (&1)`; `aff_coord 2 0`; `aff_coord 2 1`;
                `aff_const 2 (FST(P:real#real))`; `aff_const 2 (SND(P:real#real))`;
                `[lcx c s u v a; lcy c s u v a]`] AO_INSIDE_FORMS_SOUND) THEN
  REWRITE_TAC[PR_COORD2; AO_AFF_EVAL_CONST; psub; FST; SND] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[AR_REFERENCE_CHECKED; REAL_LT_01] THEN
  ASM_REWRITE_TAC[GSYM point_forms]);;

(* Lean: structure PoseRoot *)
let pose_root_INDUCT,pose_root_RECURSION = define_type "pose_root = PoseRoot angle_enc rtree";;
let pr_angle = define `pr_angle (PoseRoot w t) = w`;;
let pr_tree = define `pr_tree (PoseRoot w t) = t`;;

(* Lean: PoseRoot.Check, with the subtype check of angle *)
let proot_check = new_definition
 `proot_check r inside outside <=>
    ae_check (pr_angle r) /\
    rtree_check (pose_inputs (pr_angle r) inside) (pose_forbidden (pr_angle r) outside) (pr_tree r)`;;

(* Lean: PoseRoot.sound *)
let PR_POSEROOT_SOUND = prove
 (`forall r inside outside c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     proot_check r inside outside /\ c = normalC t /\ s = normalS t /\
     ae_lower (pr_angle r) <= t /\ t <= ae_upper (pr_angle r) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P inside ==> linside c s u v a (FST P) (SND P)) /\
     (forall P. MEM P outside ==> ~linside c s u v a (FST P) (SND P))
     ==> exists leaf. MEM leaf (rtree_leaves (pose_inputs (pr_angle r) inside) (pr_tree r)) /\
                forall f. MEM f leaf ==> lc_holds f [lcx c s u v a; lcy c s u v a]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[proot_check] THEN STRIP_TAC THEN PB_FLIP_NORMAL_TAC THEN
  MATCH_MP_TAC RT_SOUND THEN
  EXISTS_TAC `pose_forbidden (pr_angle r) outside` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PR_POSEINPUTS_SOUND THEN
    MAP_EVERY EXISTS_TAC [`t:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PR_POSEFORBIDDEN_SOUND THEN
    MAP_EVERY EXISTS_TAC [`t:real`] THEN ASM_REWRITE_TAC[]]);;
