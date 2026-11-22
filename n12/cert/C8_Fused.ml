(* ========================================================================= *)
(* W-C898, part 3: the fused 7-square chord of C898 (steps 9-10).            *)
(* Lean: Cases/C898/ChordFusedGeometry.lean (central_center_bounds,          *)
(*       left_window, right_window, lowerCut, upperCut, cutRows,             *)
(*       cutRows_hold), ChordFusedPlans.lean (DirectPlan, DirectPlan.Check,  *)
(*       DirectPlan.sound, direct_cover), ChordPlans.lean (Neighbor,         *)
(*       Neighbor.Check, Neighbor.sound, neighbor_cover_sound),              *)
(*       ChordFusedNeighbors.lean, ChordFusedData.lean, ChordFused.lean      *)
(*       (chord_fused).  Tag C8_ / c8_.                                      *)
(*                                                                           *)
(* Neighbours reuse the W-CHORD record ChNbr (hz = F): Lean's two            *)
(* RowSupport.Check on pose rows lowerLeft/lowerRight, upperLeft/upperRight  *)
(* are the hints RhPair i j at the positions of those rows in the pose.      *)
(* Lean's DirectPlan (supports / old rows) becomes one RelaxationHints hint  *)
(* per target row on the inputs cutRows = lowerCut :: upperCut :: rows       *)
(* (RhCopy (2 + position) for an old row, RhPair left right for a support);  *)
(* a closing plan proves Lean's upper (leftHi + r) false (row cl) from two   *)
(* cut rows.                                                                 *)
(* ========================================================================= *)

needs "n12/cert/C8_Pairs.ml";;

(* Lean: central_center_bounds *)
let C8_CENTRAL_BOUNDS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ a <= &1001 / &1000 /\
     lclosed c s u v a (&33 / &20) (&33 / &20) /\ lclosed c s u v a (&47 / &20) (&33 / &20)
     ==> &6397 / &4000 <= lcx c s u v a /\ lcx c s u v a <= &9603 / &4000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&33 / &20`; `&33 / &20`;
                `&1`; `&0`] TSS_CLOSED_SUPPORT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&47 / &20`; `&33 / &20`;
                `&1`; `&0`] TSS_CLOSED_SUPPORT) THEN
  ASM_REWRITE_TAC[tss_support_radius; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID;
                  REAL_MUL_LNEG; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `a / &2 * (abs c + abs s) <= &3003 / &4000` MP_TAC THENL
   [SUBGOAL_THEN `abs c + abs s <= &3 / &2` ASSUME_TAC THENL
     [MP_TAC(SPEC `c:real` REAL_POW2_ABS) THEN MP_TAC(SPEC `s:real` REAL_POW2_ABS) THEN
      MP_TAC(SPEC `c:real` REAL_ABS_POS) THEN MP_TAC(SPEC `s:real` REAL_ABS_POS) THEN
      UNDISCH_TAC `c * c + s * s = &1` THEN
      SPEC_TAC(`abs c`,`A:real`) THEN SPEC_TAC(`abs s`,`B:real`) THEN
      REWRITE_TAC[REAL_POW_2] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      NLIN_TAC [SPEC `A - B:real` REAL_LE_SQUARE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= abs c + abs s` MP_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs c + abs s <= &3 / &2` THEN UNDISCH_TAC `a <= &1001 / &1000` THEN
    UNDISCH_TAC `&0 < a` THEN
    SPEC_TAC(`abs c + abs s`,`W:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    NLIN_TAC [];
    REAL_ARITH_TAC]);;

(* Lean: DirectPlan <source, target?, supports, closeLeft, closeRight> with its
   exact cutRows: C8FPlan src k lowerCut upperCut closeRow target hints *)
let c8fplan_INDUCT,c8fplan_RECURSION = define_type
  "c8fplan = C8FPlan cpose num crow crow crow (cpose option) (crhint list)";;
let c8f_src = define `c8f_src (C8FPlan p k lc uc cl t hs) = p`;;
let c8f_targets = define `c8f_targets (C8FPlan p k lc uc cl t hs) = ch_opt_list t`;;

let c8f_target_check = define
 `(c8f_target_check src (ins:crow list) cl (NONE:cpose option) hs <=> cr_hints_check ins [cl] hs) /\
  (c8f_target_check src ins cl (SOME t) hs <=>
     cp_angle src = cp_angle t /\ cr_hints_check ins (cp_rows t) hs)`;;

(* Lean: DirectPlan.Check (+ the exactness of lowerCut / upperCut / closing:
   lowerCut = lower (leftHi + r) true, upperCut = upper (rightLo - r) true,
   closing = upper (leftHi + r) false; WL = left window, WR = right window) *)
let c8f_plan_check = define
 `c8f_plan_check (ChWin hz1 lln lld lhn lhd) (ChWin hz2 rln rld rhn rhd)
                 (C8FPlan src k lc uc cl tgt hs) <=>
    &0 < lhd /\ &0 < rld /\ cp_angle src = k /\ k < 192 /\
    (let R = EL k ch_radii in
     ch_bound_ok false true (lhn * chr_rd R + chr_rn R * lhd) (lhd * chr_rd R) true lc /\
     ch_bound_ok false false (rln * chr_rd R - chr_rn R * rld) (rld * chr_rd R) true uc /\
     ch_bound_ok false false (lhn * chr_rd R + chr_rn R * lhd) (lhd * chr_rd R) false cl) /\
    c8f_target_check src (CONS lc (CONS uc (cp_rows src))) cl tgt hs`;;

let c8f_radius = define `c8f_radius (C8FPlan p k lc uc cl t hs) = chr_r (EL k ch_radii)`;;

(* Lean: DirectPlan.sound (with cutRows_hold) *)
let C8F_PLAN_SOUND = prove
 (`forall WL WR p c s u v a.
     c8f_plan_check WL WR p /\ oriented_realizes (cr_leaf (c8f_src p)) c s u v a /\
     chw_hi WL + c8f_radius p < lcx c s u v a /\ lcx c s u v a < chw_lo WR - c8f_radius p
     ==> exists t. MEM t (c8f_targets p) /\ oriented_realizes (cr_leaf t) c s u v a`,
  MATCH_MP_TAC chwin_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`hz1:bool`; `lln:int`; `lld:int`; `lhn:int`; `lhd:int`] THEN
  MATCH_MP_TAC chwin_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`hz2:bool`; `rln:int`; `rld:int`; `rhn:int`; `rhd:int`] THEN
  MATCH_MP_TAC c8fplan_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`src:cpose`; `k:num`; `lc:crow`; `uc:crow`; `cl:crow`; `tgt:cpose option`; `hs:crhint list`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c8f_plan_check; c8f_src; c8f_targets; c8f_radius; chw_lo; chw_hi;
              LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` CH_RAD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall r. MEM r (CONS lc (CONS uc (cp_rows src))) ==>
                    cr_holds r (lcx c s u v a) (lcy c s u v a)` ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[MATCH_MP CH_BOUND_HOLDS (ASSUME
        `ch_bound_ok false true (lhn * chr_rd (EL k ch_radii) + chr_rn (EL k ch_radii) * lhd)
                         (lhd * chr_rd (EL k ch_radii)) true lc`)] THEN
      ASM_SIMP_TAC[LET_DEF; LET_END_DEF; CH_Q_ADD; GSYM CHR_R];
      REWRITE_TAC[MATCH_MP CH_BOUND_HOLDS (ASSUME
        `ch_bound_ok false false (rln * chr_rd (EL k ch_radii) - chr_rn (EL k ch_radii) * rld)
                         (rld * chr_rd (EL k ch_radii)) true uc`)] THEN
      ASM_SIMP_TAC[LET_DEF; LET_END_DEF; CH_Q_SUB; GSYM CHR_R];
      ASM_MESON_TAC[CR_REALIZES_ROWS]];
    ALL_TAC] THEN
  UNDISCH_TAC `c8f_target_check src (CONS lc (CONS uc (cp_rows src))) cl tgt hs` THEN
  STRUCT_CASES_TAC(ISPEC `tgt:cpose option` (cases "option")) THEN
  REWRITE_TAC[c8f_target_check; ch_opt_list; MEM; UNWIND_THM1; UNWIND_THM2] THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`CONS (lc:crow) (CONS uc (cp_rows src))`; `[cl:crow]`; `hs:crhint list`;
                  `lcx c s u v a`; `lcy c s u v a`] CR_HINTS_SOUND) THEN
    ASM_REWRITE_TAC[MEM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[MATCH_MP CH_BOUND_HOLDS (ASSUME
        `ch_bound_ok false false (lhn * chr_rd (EL k ch_radii) + chr_rn (EL k ch_radii) * lhd)
                         (lhd * chr_rd (EL k ch_radii)) false cl`)] THEN
    ASM_SIMP_TAC[LET_DEF; LET_END_DEF; CH_Q_ADD; GSYM CHR_R] THEN
    UNDISCH_TAC `ch_q lhn lhd + chr_r (EL k ch_radii) < lcx c s u v a` THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN MATCH_MP_TAC CR_TRANSFER THEN EXISTS_TAC `src:cpose` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CR_HINTS_SOUND THEN
      MAP_EVERY EXISTS_TAC [`CONS (lc:crow) (CONS uc (cp_rows src))`; `hs:crhint list`] THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC]]);;

(* Lean: C898Chord.Fused.chord_fused (q : Fin 7 -> OpenSquare; only the disjointness
   pairs of the two windows {0,1,2,3}, {0,4,5,6} are assumed) *)
let c8_fused_transition = new_definition
 `c8_fused_transition (Sd:pose_leaf list) (N1:pose_leaf list) (N2:pose_leaf list)
     (N3:pose_leaf list) (M1:pose_leaf list) (M2:pose_leaf list) (M3:pose_leaf list)
     (Td:pose_leaf list) <=>
    forall c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 c4 s4 u4 v4 a4 c5 s5 u5 v5 a5 c6 s6 u6 v6 a6.
      c0 * c0 + s0 * s0 = &1 /\ &0 < a0 /\ &1 < a0 /\
      c1 * c1 + s1 * s1 = &1 /\ &0 < a1 /\ &1 < a1 /\
      c2 * c2 + s2 * s2 = &1 /\ &0 < a2 /\ &1 < a2 /\
      c3 * c3 + s3 * s3 = &1 /\ &0 < a3 /\ &1 < a3 /\
      c4 * c4 + s4 * s4 = &1 /\ &0 < a4 /\ &1 < a4 /\
      c5 * c5 + s5 * s5 = &1 /\ &0 < a5 /\ &1 < a5 /\
      c6 * c6 + s6 * s6 = &1 /\ &0 < a6 /\ &1 < a6 /\
      lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c2 s2 u2 v2 a2 /\ lcont c3 s3 u3 v3 a3 /\ lcont c4 s4 u4 v4 a4 /\ lcont c5 s5 u5 v5 a5 /\ lcont c6 s6 u6 v6 a6 /\
      ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\
      ldisj c0 s0 u0 v0 a0 c2 s2 u2 v2 a2 /\
      ldisj c0 s0 u0 v0 a0 c3 s3 u3 v3 a3 /\
      ldisj c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 /\
      ldisj c1 s1 u1 v1 a1 c3 s3 u3 v3 a3 /\
      ldisj c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 /\
      ldisj c0 s0 u0 v0 a0 c4 s4 u4 v4 a4 /\
      ldisj c0 s0 u0 v0 a0 c5 s5 u5 v5 a5 /\
      ldisj c0 s0 u0 v0 a0 c6 s6 u6 v6 a6 /\
      ldisj c4 s4 u4 v4 a4 c5 s5 u5 v5 a5 /\
      ldisj c4 s4 u4 v4 a4 c6 s6 u6 v6 a6 /\
      ldisj c5 s5 u5 v5 a5 c6 s6 u6 v6 a6 /\
      a0 <= &1001 / &1000 /\ lclosed c0 s0 u0 v0 a0 (&33 / &20) (&33 / &20) /\
      lclosed c0 s0 u0 v0 a0 (&47 / &20) (&33 / &20) /\
      oriented_pose_covered Sd c0 s0 u0 v0 a0 /\
      oriented_pose_covered N1 c1 s1 u1 v1 a1 /\
      oriented_pose_covered N2 c2 s2 u2 v2 a2 /\
      oriented_pose_covered N3 c3 s3 u3 v3 a3 /\
      oriented_pose_covered M1 c4 s4 u4 v4 a4 /\
      oriented_pose_covered M2 c5 s5 u5 v5 a5 /\
      oriented_pose_covered M3 c6 s6 u6 v6 a6
      ==> oriented_pose_covered Td c0 s0 u0 v0 a0`;;

let c8f_plan_ok = new_definition
 `c8f_plan_ok WL WR (Td:cpose list) p <=>
    c8f_plan_check WL WR p /\ ALL (\t. MEM t Td) (c8f_targets p)`;;

let C8F_PLAN_RADIUS = prove
 (`forall WL WR p. c8f_plan_check WL WR p
     ==> &0 <= c8f_radius p /\ ae_check (pl_angle (cr_leaf (c8f_src p))) /\
         ch_radius_check (chr_B (EL (cp_angle (c8f_src p)) ch_radii)) (c8f_radius p)
                         (pl_angle (cr_leaf (c8f_src p)))`,
  MATCH_MP_TAC chwin_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`hz1:bool`; `lln:int`; `lld:int`; `lhn:int`; `lhd:int`] THEN
  MATCH_MP_TAC chwin_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`hz2:bool`; `rln:int`; `rld:int`; `rhn:int`; `rhd:int`] THEN
  MATCH_MP_TAC c8fplan_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[c8f_plan_check; c8f_radius; c8f_src; CH_LEAF_ANGLE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try fst(dest_const(rator(lhs(concl th)))) = "cp_angle" with Failure _ -> false)) THEN
  ASM_SIMP_TAC[CH_RAD_FACTS]);;

let CH_CENTER_V = prove
 (`forall c s u v a. ch_center false c s u v a = lcx c s u v a`, REWRITE_TAC[ch_center]);;

(* Lean: chord_fused (with left_window, right_window, direct_cover) *)
let C8_FUSED_SOUND = prove
 (`forall WL WR n1 n2 n3 m1 m2 m3 plans Sd Td.
     ~(chw_hz WL) /\ ~(chw_hz WR) /\ chw_lo WL <= chw_hi WL /\ chw_lo WR <= chw_hi WR /\
     chw_lo WL <= &6397 / &4000 /\ &9603 / &4000 <= chw_hi WR /\
     ALL (ch_nbr_check WL) n1 /\ ALL (ch_nbr_check WL) n2 /\ ALL (ch_nbr_check WL) n3 /\
     ALL (ch_nbr_check WR) m1 /\ ALL (ch_nbr_check WR) m2 /\ ALL (ch_nbr_check WR) m3 /\
     ALL (c8f_plan_ok WL WR Td) plans /\ MAP c8f_src plans = Sd
     ==> c8_fused_transition (MAP cr_leaf Sd)
           (MAP cr_leaf (MAP chn_src n1)) (MAP cr_leaf (MAP chn_src n2)) (MAP cr_leaf (MAP chn_src n3))
           (MAP cr_leaf (MAP chn_src m1)) (MAP cr_leaf (MAP chn_src m2)) (MAP cr_leaf (MAP chn_src m3))
           (MAP cr_leaf Td)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c8_fused_transition] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `oriented_pose_covered (MAP cr_leaf Sd) c0 s0 u0 v0 a0` THEN
  REWRITE_TAC[oriented_pose_covered; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:pose_leaf` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `src:cpose` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `exists p. MEM p plans /\ c8f_src p = src` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (src:cpose) Sd` THEN EXPAND_TAC "Sd" THEN
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `ALL (c8f_plan_ok WL WR Td) plans` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `p:c8fplan`) THEN ASM_REWRITE_TAC[c8f_plan_ok; GSYM ALL_MEM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `c8f_src p = src`)) THEN
  MP_TAC(SPECL [`WL:chwin`; `WR:chwin`; `p:c8fplan`] C8F_PLAN_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`] C8_CENTRAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall cut. chw_lo WL <= cut /\ cut <= chw_hi WL ==>
     ch_section false c1 s1 u1 v1 a1 cut /\ ch_section false c2 s2 u2 v2 a2 cut /\
     ch_section false c3 s3 u3 v3 a3 cut` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBST1_TAC(SYM(EQF_INTRO(ASSUME `~(chw_hz WL)`))) THEN
    MATCH_MP_TAC CH_NBR_COVER THENL
     [EXISTS_TAC `n1:chnbr list`; EXISTS_TAC `n2:chnbr list`; EXISTS_TAC `n3:chnbr list`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `forall cut. chw_lo WR <= cut /\ cut <= chw_hi WR ==>
     ch_section false c4 s4 u4 v4 a4 cut /\ ch_section false c5 s5 u5 v5 a5 cut /\
     ch_section false c6 s6 u6 v6 a6 cut` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBST1_TAC(SYM(EQF_INTRO(ASSUME `~(chw_hz WR)`))) THEN
    MATCH_MP_TAC CH_NBR_COVER THENL
     [EXISTS_TAC `m1:chnbr list`; EXISTS_TAC `m2:chnbr list`; EXISTS_TAC `m3:chnbr list`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`false`; `chw_lo WL`; `chw_hi WL`; `cr_leaf (c8f_src p)`;
                `chr_B (EL (cp_angle (c8f_src p)) ch_radii)`; `c8f_radius p`;
                `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`; `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`; `c2:real`; `s2:real`; `u2:real`; `v2:real`; `a2:real`; `c3:real`; `s3:real`; `u3:real`; `v3:real`; `a3:real`] CH_WINDOW_EXCLUDES) THEN
  MP_TAC(SPECL [`false`; `chw_lo WR`; `chw_hi WR`; `cr_leaf (c8f_src p)`;
                `chr_B (EL (cp_angle (c8f_src p)) ch_radii)`; `c8f_radius p`;
                `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`; `c4:real`; `s4:real`; `u4:real`; `v4:real`; `a4:real`; `c5:real`; `s5:real`; `u5:real`; `v5:real`; `a5:real`; `c6:real`; `s6:real`; `u6:real`; `v6:real`; `a6:real`] CH_WINDOW_EXCLUDES) THEN
  ASM_REWRITE_TAC[CH_CENTER_V] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`WL:chwin`; `WR:chwin`; `p:c8fplan`; `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`] C8F_PLAN_SOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:cpose` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_leaf t` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:cpose` THEN
  ASM_MESON_TAC[]);;

let () =
  cr_extra_thms := !cr_extra_thms @
    [c8f_src; c8f_targets; c8f_target_check; c8f_plan_check; injectivity "c8fplan"];
  cr_cs_reset ();;
