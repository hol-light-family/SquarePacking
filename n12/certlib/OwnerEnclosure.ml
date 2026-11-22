(* ========================================================================= *)
(* Port of source/S12/OwnerEnclosure.lean (Jatloe, N12-jatloe).              *)
(* PoseLeaf <angle, inputs> is PoseLeaf angle inputs (angle : angle_enc,     *)
(* inputs : lincon list).  The Lean subtype {w // w.Check} of the angle is   *)
(* not part of the HOL value; where Lean uses it, it is supplied by the      *)
(* checks of the containing structures (proot_check, oe_check, ...).         *)
(* exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME (geometry/WallCenterBarrier).*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/certlib/PoseRegion.ml";;
needs "n12/certlib/IntervalCoverage.ml";;

(* Lean: structure PoseLeaf *)
let pose_leaf_INDUCT,pose_leaf_RECURSION =
  define_type "pose_leaf = PoseLeaf angle_enc (lincon list)";;
let pl_angle = define `pl_angle (PoseLeaf w l) = w`;;
let pl_inputs = define `pl_inputs (PoseLeaf w l) = l`;;

(* Lean: PoseLeaf.Realizes *)
let pose_realizes = new_definition
 `pose_realizes leaf c s u v a <=>
    (forall f. MEM f (pl_inputs leaf) ==> lc_holds f [lcx c s u v a; lcy c s u v a]) /\
    (forall P. psub P (lcx c s u v a, lcy c s u v a) IN rs_sqset (ae_reference (pl_angle leaf) (&1))
         ==> P IN sqset c s u v a)`;;

(* Lean: PoseRoot.leaves *)
let proot_leaves = new_definition
 `proot_leaves r inside =
    MAP (\inputs. PoseLeaf (pr_angle r) inputs)
        (rtree_leaves (pose_inputs (pr_angle r) inside) (pr_tree r))`;;

(* Lean: structure OwnerEnclosure *)
let owner_enc_INDUCT,owner_enc_RECURSION =
  define_type "owner_enc = OwnerEnc ((real#real)list) ((real#real)list) (pose_root list)";;
let oe_inside = define `oe_inside (OwnerEnc i ou r) = i`;;
let oe_outside = define `oe_outside (OwnerEnc i ou r) = ou`;;
let oe_roots = define `oe_roots (OwnerEnc i ou r) = r`;;

(* Lean: OwnerEnclosure.Check, with the subtype checks of the roots *)
let oe_check = new_definition
 `oe_check w <=>
    covers_interval (&0) (&1) (MAP pr_angle (oe_roots w)) /\
    forall r. MEM r (oe_roots w) ==> proot_check r (oe_inside w) (oe_outside w)`;;

(* Lean: OwnerEnclosure.leaves *)
let oe_leaves = new_definition
 `oe_leaves w = lflat (MAP (\r. proot_leaves r (oe_inside w)) (oe_roots w))`;;

(* The common core of OwnerEnclosure.sound and OwnerEnclosure.oriented_sound:
   the leaf found also carries the face indexing and half-angle witness. *)
let OE_SOUND_WITNESS = prove
 (`forall w c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     oe_check w /\ &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P (oe_inside w) ==> linside c s u v a (FST P) (SND P)) /\
     (forall P. MEM P (oe_outside w) ==> ~linside c s u v a (FST P) (SND P))
     ==> exists leaf. MEM leaf (oe_leaves w) /\ pose_realizes leaf c s u v a /\
                exists c' s' u' v' a' t.
                  c' * c' + s' * s' = &1 /\ &0 < a' /\
                  c' = normalC t /\ s' = normalS t /\
                  ae_lower (pl_angle leaf) <= t /\ t <= ae_upper (pl_angle leaf) /\
                  a' = a /\ lcx c' s' u' v' a' = lcx c s u v a /\
                  lcy c' s' u' v' a' = lcy c s u v a /\
                  (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oe_check] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`s':real`; `c':real`] AE_FIRST_QUADRANT_RATIONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[GSYM normalS])
                     (ASSUME_TAC o REWRITE_RULE[GSYM normalC]))))) THEN
  MP_TAC(SPECL [`MAP pr_angle (oe_roots w)`; `&0`; `&1`; `t:real`] IC_COVERSINTERVAL_SOUND) THEN
  ASM_REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `ang:angle_enc` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `root:pose_root` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `ang = pr_angle root` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `proot_check root (oe_inside w) (oe_outside w)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`root:pose_root`; `oe_inside w`; `oe_outside w`; `c':real`; `s':real`;
                `u':real`; `v':real`; `a':real`; `t:real`] PR_POSEROOT_SOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `inputs:lincon list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `PoseLeaf (pr_angle root) inputs` THEN
  REWRITE_TAC[pl_angle; pl_inputs; pose_realizes] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[oe_leaves; MEM_LFLAT; MEM_MAP; proot_leaves] THEN
    EXISTS_TAC `MAP (\inputs. PoseLeaf (pr_angle root) inputs)
       (rtree_leaves (pose_inputs (pr_angle root) (oe_inside w)) (pr_tree root))` THEN
    CONJ_TAC THENL [EXISTS_TAC `root:pose_root` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `inputs:lincon list` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `P:real#real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`pr_angle root`; `&1`; `c':real`; `s':real`; `u':real`; `v':real`;
                  `a':real`; `t:real`] AR_INNER_SOUND) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `proot_check root (oe_inside w) (oe_outside w)` THEN
      REWRITE_TAC[proot_check] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `P:real#real`) THEN ASM_REWRITE_TAC[IN_SQSET];
    MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `t:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: OwnerEnclosure.sound *)
let OE_SOUND = prove
 (`forall w c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     oe_check w /\ &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P (oe_inside w) ==> linside c s u v a (FST P) (SND P)) /\
     (forall P. MEM P (oe_outside w) ==> ~linside c s u v a (FST P) (SND P))
     ==> exists leaf. MEM leaf (oe_leaves w) /\ pose_realizes leaf c s u v a`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP OE_SOUND_WITNESS) THEN MESON_TAC[]);;

(* Lean: structure OwnerPairCertificate *)
let owner_pair_INDUCT,owner_pair_RECURSION =
  define_type "owner_pair = OwnerPair owner_enc owner_enc (affcert list)";;
let op_first = define `op_first (OwnerPair f s ov) = f`;;
let op_second = define `op_second (OwnerPair f s ov) = s`;;
let op_overlaps = define `op_overlaps (OwnerPair f s ov) = ov`;;

(* Lean: OwnerPairCertificate.Check, with the subtype checks of its fields *)
let op_check = new_definition
 `op_check w <=>
    oe_check (op_first w) /\ oe_check (op_second w) /\
    (forall c. MEM c (op_overlaps w) ==> affcert_check c) /\
    forall a. MEM a (oe_leaves (op_first w)) ==> forall b. MEM b (oe_leaves (op_second w)) ==>
      exists c. MEM c (op_overlaps w) /\
          ac_first c = ae_reference (pl_angle a) (&1) /\
          ac_second c = ae_reference (pl_angle b) (&1) /\
          ac_inputsA c = pl_inputs a /\ ac_inputsB c = pl_inputs b`;;

(* Lean: OwnerPairCertificate.sound *)
let OE_OWNERPAIR_SOUND = prove
 (`forall w cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     op_check w /\ &1 < aq /\ &1 < ar /\ aq <= &1001 / &1000 /\ ar <= &1001 / &1000 /\
     lcont cq sq uq vq aq /\ lcont cr sr ur vr ar /\
     (forall P. MEM P (oe_inside (op_first w)) ==> linside cq sq uq vq aq (FST P) (SND P)) /\
     (forall P. MEM P (oe_outside (op_first w)) ==> ~linside cq sq uq vq aq (FST P) (SND P)) /\
     (forall P. MEM P (oe_inside (op_second w)) ==> linside cr sr ur vr ar (FST P) (SND P)) /\
     (forall P. MEM P (oe_outside (op_second w)) ==> ~linside cr sr ur vr ar (FST P) (SND P)) /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[op_check] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`op_first w`; `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] OE_SOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `la:pose_leaf` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`op_second w`; `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] OE_SOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `lb:pose_leaf` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `la:pose_leaf` o check (fun th ->
    can (find_term ((=) `ac_inputsA`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `lb:pose_leaf`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `cc:affcert` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cc:affcert`; `lcx cq sq uq vq aq`; `lcy cq sq uq vq aq`;
                `lcx cr sr ur vr ar`; `lcy cr sr ur vr ar`] AO_SOUND) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pose_realizes]) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[overlaps_at; NOT_EXISTS_THM] THEN X_GEN_TAC `P:real#real` THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cq sq uq vq aq cr sr ur vr ar` THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(P:real#real)`; `SND(P:real#real)`]) THEN
  REWRITE_TAC[GSYM IN_SQSET] THEN ASM_MESON_TAC[]);;
