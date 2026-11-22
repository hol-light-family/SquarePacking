(* ========================================================================= *)
(* W-CHORD, part 2: the C713 occupied-row height stage (step 5).            *)
(* Lean: Compact/Bridge/VertexCutRelaxation.lean (containerRows, Spec,       *)
(*       Spec.base, Spec.targets, Spec.Check, Spec.sound),                   *)
(*       Compact/Cases/C713/HeightCore.lean (Entry, Entry.Check,             *)
(*       Entry.cut_holds), Compact/Bridge/OccupiedRowChord.lean              *)
(*       (above_radius), Compact/Cases/C713/OccupiedRow.lean (above_radius,  *)
(*       square level), Compact/Cases/C713/ChordDirect.lean                  *)
(*       (source_to_after_height, square level), HeightData/{Batch*,All}.    *)
(* Design: n12/docs/cert_design.md §4.4.  Tag CH_ / ch_.                         *)
(*                                                                           *)
(* Checker choice.  Lean checks each record by planar vertex enumeration     *)
(* (PlanarVertexSparse.UnorderedCheck base [] targets).  The base region has *)
(* no forbidden blocks (closed convex polygon), so every target row follows  *)
(* by a <=2-row Farkas certificate or the polygon is empty (<=3 rows).  The  *)
(* HOL record carries such certificates (BlockedTarget hints with an empty   *)
(* block, found by n12/scripts/cert_oracle_height.py) and is checked by F1       *)
(* (cr_bt_check); this proves Spec.sound's conclusion without F6.            *)
(* ========================================================================= *)

needs "n12/cert/CH_Chord.ml";;

(* Lean: VertexCutRelaxation.containerRows *)
let ch_container_rows = new_definition
 `ch_container_rows =
    [CRow (&1) (&0) (&0) false; CRow (-- &1) (&0) (&4) false;
     CRow (&0) (&1) (&0) false; CRow (&0) (-- &1) (&4) false]`;;

(* Lean: containerRows_hold *)
let CH_CONTAINER_HOLD = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ lcont c s u v a
     ==> forall r. MEM r ch_container_rows ==> cr_holds r (lcx c s u v a) (lcy c s u v a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] SSB_SQUARE_CENTER_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
  DISCH_THEN(MP_TAC o SPECL [`lcx c s u v a`; `lcy c s u v a`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[ch_container_rows; MEM] THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s] THEN
  REWRITE_TAC[int_of_num_th; int_neg_th] THEN ASM_REAL_ARITH_TAC);;

(* Lean: C713Height.Entry  (Spec <source, cut, target>, radius = table entry k) + hints *)
let chheight_INDUCT,chheight_RECURSION = define_type
  "chheight = ChHeight cpose crow (cpose option) num (cbhint list)";;
let chh_src = define `chh_src (ChHeight p cut t k hs) = p`;;
let ch_opt_list = define `(ch_opt_list (NONE:cpose option) = []) /\ (ch_opt_list (SOME t) = [t])`;;
let chh_targets = define `chh_targets (ChHeight p cut t k hs) = ch_opt_list t`;;

(* Lean: Spec.base *)
let ch_hbase = new_definition
 `ch_hbase src cut = APPEND (CONS cut (cp_rows src)) ch_container_rows`;;

(* Lean: Spec.targets *)
let ch_htargets = define
 `(ch_htargets NONE = [CRow (&0) (&0) (-- &1) false]) /\ (ch_htargets (SOME t) = cp_rows t)`;;

let ch_tgt_angle = define
 `(ch_tgt_angle src (NONE:cpose option) <=> true) /\
  (ch_tgt_angle src (SOME t) <=> cp_angle src = cp_angle t)`;;

(* Lean: Entry.Check (Spec.Check with F1 certificates in place of the vertex check) *)
let ch_height_check = define
 `ch_height_check (ChHeight src cut tgt k hs) <=>
    cp_angle src = k /\ k < 192 /\
    (let R = EL k ch_radii in
     &0 < chr_rd R /\ cr_x cut = &0 /\ ~(cr_s cut) /\ &0 < cr_y cut /\
     cr_c cut * (&50 * chr_rd R) + cr_y cut * (&87 * chr_rd R + &50 * chr_rn R) = &0) /\
    cr_bt_check (ch_hbase src cut) [] (ch_htargets tgt) hs /\ ALL cr_bhint_indep hs /\
    ch_tgt_angle src tgt`;;

let chh_radius = define `chh_radius (ChHeight src cut tgt k hs) = chr_r (EL k ch_radii)`;;

let CH_CUT_ALG = prove
 (`forall C Y n d py. &0 < d /\ &0 < Y /\ C * &50 * d + Y * (&87 * d + &50 * n) = &0 /\
                &87 / &50 + n / d < py ==> &0 <= Y * py + C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Y * py + C = Y * (py - (&87 / &50 + n / d))` SUBST1_TAC THENL
   [UNDISCH_TAC `C * &50 * d + Y * (&87 * d + &50 * n) = &0` THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* Lean: Entry.cut_holds *)
let CH_HEIGHT_CUT = prove
 (`forall src cut tgt k hs px py.
     ch_height_check (ChHeight src cut tgt k hs) /\
     &87 / &50 + chr_r (EL k ch_radii) < py ==> cr_holds cut px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ch_height_check; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[cr_holds; cr_eval] THEN
  RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MP_TAC(SPECL [`real_of_int (cr_c cut)`; `real_of_int (cr_y cut)`;
    `real_of_int (chr_rn (EL k ch_radii))`; `real_of_int (chr_rd (EL k ch_radii))`; `py:real`]
    CH_CUT_ALG) THEN
  ASM_REWRITE_TAC[GSYM ch_q; GSYM CHR_R] THEN
  REWRITE_TAC[int_of_num_th; REAL_MUL_LZERO; REAL_ADD_LID]);;

(* Lean: VertexCutRelaxation.Spec.sound *)
let CH_HEIGHT_SPEC_SOUND = prove
 (`forall src cut tgt k hs c s u v a.
     ch_height_check (ChHeight src cut tgt k hs) /\ c * c + s * s = &1 /\ &0 < a /\
     oriented_realizes (cr_leaf src) c s u v a /\ lcont c s u v a /\
     cr_holds cut (lcx c s u v a) (lcy c s u v a)
     ==> exists t. MEM t (ch_opt_list tgt) /\ oriented_realizes (cr_leaf t) c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ch_height_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ch_height_check" with Failure _ -> false)) THEN
  MP_TAC(SPECL [`ch_hbase src cut`; `[]:crow list`; `ch_htargets tgt`; `hs:cbhint list`;
                `lcx c s u v a`; `lcy c s u v a`] CR_BT_SOURCE_SOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(SPECL [`src:cpose`; `c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
      CR_REALIZES_ROWS) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CH_CONTAINER_HOLD) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[ch_hbase; MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ch_tgt_angle src tgt` THEN
  STRUCT_CASES_TAC(ISPEC `tgt:cpose option` (cases "option")) THEN
  REWRITE_TAC[ch_htargets; ch_tgt_angle; ch_opt_list; MEM; UNWIND_THM1; UNWIND_THM2;
              FORALL_UNWIND_THM2] THENL
   [REWRITE_TAC[cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s; int_of_num_th; int_neg_th] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CR_TRANSFER THEN EXISTS_TAC `src:cpose` THEN
    ASM_MESON_TAC[]]);;

let CH_LINSIDE_CLOSED = prove
 (`forall c s u v a x y. linside c s u v a x y ==> lclosed c s u v a x y`,
  REWRITE_TAC[linside; lclosed] THEN REAL_ARITH_TAC);;

(* Lean: OccupiedRowChord.above_radius *)
let CH_OCCUPIED_ABOVE = prove
 (`forall leaf B r c s u v a (cN:num->real) sN uN vN aN h x y.
     ae_check (pl_angle leaf) /\ ch_radius_check B r (pl_angle leaf) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\ angle_witness leaf c s u v a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     linside c s u v a x y /\ h + &51 / &100 <= y /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) h) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\ linside (cN i) (sN i) (uN i) (vN i) (aN i) x y))
     ==> h + r < lcy c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle_witness] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `a':real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ae_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ae_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_NONNEGATIVE) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPECL [`B:real`; `r:real`; `pl_angle leaf`; `t:real`] CH_RADIUS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r <= lsec_radius c' s'` ASSUME_TAC THENL
   [REWRITE_TAC[lsec_radius; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[real_abs] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`;
                `cN:num->real`; `sN:num->real`; `uN:num->real`; `vN:num->real`; `aN:num->real`;
                `h:real`; `x:real`; `y:real`] CBH_FROM_THREE_OCCUPIED_POINTS) THEN
  ANTS_TAC THENL
   [    MP_TAC(ASSUME `forall x y. linside c' s' u' v' a x y <=> linside c s u v a x y`) THEN
    DISCH_THEN(fun iff ->
      REPEAT CONJ_TAC THEN REWRITE_TAC[iff] THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont; iff] THEN NO_TAC) THEN
      MATCH_MP_TAC CH_LINSIDE_CLOSED THEN REWRITE_TAC[iff] THEN FIRST_ASSUM ACCEPT_TAC);
    ASM_REAL_ARITH_TAC]);;

let ch_height_ok = new_definition
 `ch_height_ok (Td:cpose list) h <=> ch_height_check h /\ ALL (\t. MEM t Td) (chh_targets h)`;;

(* Lean: C713ChordDirect.source_to_after_height, with the occupied-row points of
   C713OccupiedRow.above_radius as premises (neighbours = masks 2, 512, 16384,
   cN i at the point (i+1, 87/50); owner 2304 contains (33/20, 47/20)). *)
let CH_HEIGHT_STAGE = prove
 (`forall hs Sd Td. ALL (ch_height_ok Td) hs /\ MAP chh_src hs = Sd ==>
   forall c s u v a (cN:num->real) sN uN vN aN.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) (&87 / &50)) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\ linside (cN i) (sN i) (uN i) (vN i) (aN i) x y)) /\
     oriented_pose_covered (MAP cr_leaf Sd) c s u v a
     ==> oriented_pose_covered (MAP cr_leaf Td) c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `oriented_pose_covered (MAP cr_leaf Sd) c s u v a` THEN
  REWRITE_TAC[oriented_pose_covered; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:pose_leaf` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `src:cpose` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `exists e. MEM e hs /\ chh_src e = src` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (src:cpose) Sd` THEN EXPAND_TAC "Sd" THEN
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `ALL (ch_height_ok Td) hs` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:chheight`) THEN ASM_REWRITE_TAC[ch_height_ok; GSYM ALL_MEM] THEN
  UNDISCH_TAC `chh_src e = src` THEN
  SPEC_TAC(`e:chheight`,`e:chheight`) THEN MATCH_MP_TAC chheight_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`p:cpose`; `cut:crow`; `tg:cpose option`; `k:num`; `hh:cbhint list`] THEN
  REWRITE_TAC[chh_src; chh_targets] THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ch_height_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ch_height_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `k:num` CH_RAD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cr_leaf src`; `chr_B (EL k ch_radii)`; `chr_r (EL k ch_radii)`;
                `c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cN:num->real`; `sN:num->real`; `uN:num->real`; `vN:num->real`; `aN:num->real`;
                `&87 / &50`; `&33 / &20`; `&47 / &20`] CH_OCCUPIED_ABOVE) THEN
  ASM_REWRITE_TAC[CH_LEAF_ANGLE] THEN ANTS_TAC THENL
   [UNDISCH_TAC `oriented_realizes (cr_leaf src) c s u v a` THEN
    SIMP_TAC[oriented_realizes] THEN DISCH_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`src:cpose`; `cut:crow`; `tg:cpose option`; `k:num`; `hh:cbhint list`;
                `lcx c s u v a`; `lcy c s u v a`] CH_HEIGHT_CUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`src:cpose`; `cut:crow`; `tg:cpose option`; `k:num`; `hh:cbhint list`;
                `c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CH_HEIGHT_SPEC_SOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:cpose` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_leaf t` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:cpose` THEN
  ASM_MESON_TAC[]);;

let () =
  cr_extra_thms := !cr_extra_thms @
    [ch_container_rows; ch_hbase; ch_htargets; ch_tgt_angle; ch_height_check;
     ch_opt_list; chh_targets; chh_src];
  cr_cs_reset ();;
