(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualRightNear.lean                 *)
(* (N12Compact.C1092MPPMActualRightNear).  The actual right-near entrance in *)
(* the normalized MPPM one-omission branch.  Conventions and forward toolkit *)
(* of CP_C1092_MPPMOmissionCenter.ml (c1092moc_ functions; owners p i at     *)
(* mask EL i c1092wc_code, side l; WallContext p mppm is C1092MPPE_CTX,      *)
(* omitted is C1092MPPE_OMIT; near is C1092MARN_NEAR).  The private side_gt /*)
(* side_same / mark are C1092MOC_SIDE_GT / SIDE_SAME / oo_seed markers.      *)
(* PositiveInward p C is c1092marn_pos c1 c2 a b l cC sC uC vC aC (with the  *)
(* OpenSquare invariants).  (pullX q).translated 2 2 is the layered tuple    *)
(* C1092MARN_T7 / C1092MARN_TW (equivalences C1092MARN_EQ7 / EQW), pullX     *)
(* (pullSwap q) is C1092MARN_TB / TK.  wall_auxiliaries                      *)
(* C1092MPPE_WALL_AUXILIARIES; MPPMRightInner.other_ordinary                 *)
(* C1092MPRI_OTHER_ORDINARY; C1092AuxiliaryCover.northwest_f/g_cover         *)
(* C1092AC_NORTHWEST_F/G_COVER; C1092MixedSpan.impossible C1092MS_IMPOSSIBLE;*)
(* MMMPShortBarNegative.impossible C1092SBN_IMPOSSIBLE;                      *)
(* MPPMOmissionCenter.bottom_center C1092MOC_BOTTOM_CENTER;                  *)
(* MPPMUpperOrigin.top_origin C1092MPUO_TOP_ORIGIN; WallProfile.             *)
(* boundary_origin OCWPBO_BOUNDARY_ORIGIN; MMMPInwardOuterArmHalfpoint.point *)
(* C1092MIOA_POINT; MMMPBottomOriginObstruction.impossible                   *)
(* C1092BOO_IMPOSSIBLE; corner_points via oo_seed at (1,3).                  *)
(* (Lean header: "Source only, uncompiled".)  Tag C1092MARN_.                *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualOneOmission.ml";;
needs "n12/geometry/CP_C1092_MMMP_ShortBarNegative.ml";;
needs "n12/geometry/CP_C1092_MMMP_InwardOuterArmHalfpoint.ml";;
needs "n12/geometry/CP_C1092_MMMP_BottomOriginObstruction.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

let C1092MARN_NEAR = c1092mppe_in 11 "&87 / &50" "&3";;
let C1092MARN_NEAR_TM = parse_term C1092MARN_NEAR;;
let C1092MARN_HYPS = Printf.sprintf "%s /\\ %s" C1092MPRI_HYPS C1092MARN_NEAR;;

(* use an EL-form packing theorem whose hypotheses are among NPACK, IMAGE, ctx, omitted, near *)
let c1092marn_use th =
  let th1 = SPECL C1092MPPE_V th in
  let hs = [C1092MOC_NP; C1092MOC_IMG; C1092MOC_CTX; C1092MOC_OMIT; C1092MARN_NEAR_TM] in
  let rec build tm = if mem tm hs then ASSUME tm else
    let l, r = dest_conj tm in CONJ (build l) (build r) in
  CONV_RULE C1092MOC_CODE_CONV (MP th1 (build (lhand (concl th1))));;
let c1092marn_near () = CONV_RULE C1092MOC_CODE_CONV (ASSUME C1092MARN_NEAR_TM);;

(* layered tuples and their plain equivalences *)
let c1092marn_equiv t i fx fy =
  let x = `x:real` and y = `y:real` in
  prove(list_mk_forall([x; y], mk_eq(list_mk_comb(`linside`, t @ [x; y]),
                                     list_mk_comb(`linside`, c1092moc_own i @ [fx; fy]))),
        REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1092MARN_T7 = fst (c1092moc_layers 7 [C1092MOC_X; c1092moc_tr `&2` `&2`]);;
let C1092MARN_TW = fst (c1092moc_layers 8 [C1092MOC_X; c1092moc_tr `&2` `&2`]);;
let C1092MARN_TB = fst (c1092moc_layers 8 [C1092MOC_SW; C1092MOC_X]);;
let C1092MARN_TK = fst (c1092moc_layers 3 [C1092MOC_SW; C1092MOC_X]);;
let C1092MARN_EQ7 = c1092marn_equiv C1092MARN_T7 7 `&2 - x` `&2 + y`;;
let C1092MARN_EQW = c1092marn_equiv C1092MARN_TW 8 `&2 - x` `&2 + y`;;
let C1092MARN_EQB = c1092marn_equiv C1092MARN_TB 8 `y:real` `&4 - x`;;
let C1092MARN_EQK = c1092marn_equiv C1092MARN_TK 3 `y:real` `&4 - x`;;

(* the C square of a positive inward frame (side l after substitution) *)
let C1092MARN_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`];;
let c1092marn_cin x y = list_mk_comb(`linside`, C1092MARN_CV @ [x; y]);;
let c1092marn_win x y = list_mk_comb(`linside`, C1092MARN_TW @ [x; y]);;
let C1092MARN_ACT_TM =
  let x = `x:real` and y = `y:real` in
  list_mk_forall([x; y], mk_eq(c1092marn_cin x y,
    list_mk_comb(`linside`, c1092moc_own 7 @ [`&2 - x`; `&2 + y`])));;

(* add a fact tm, proved from th through the equivalences eqs *)
let c1092marn_cf eqs tm th =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC eqs THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    (fun g -> try ACCEPT_TAC th g with Failure _ ->
       failwith ("c1092marn_cf: " ^ string_of_term (snd g) ^ " FROM " ^ string_of_term (concl th)));
    ALL_TAC];;
let C1092MARN_CLOSE_TAC =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; RASM_ARITH_TAC];;

(* the left wall cut (hb 0).1 *)
let C1092MARN_LEFT_CUT = prove
 (`forall c1 c2 a b l. c1092wc_ctx c1 c2 a b l c1092mppe_mppm
     ==> &2 <= lcy (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096)
                   (oov c1 c2 a b l 4096) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[c1092mppe_mppm; ARITH] THEN
  REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092WC_CODE_EL) THEN
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

let C1092MARN_LEFT_TIP = c1092mppe_wall_point 0 `&161 / &100` "&1" "&239 / &100";;

(* Lean: inward_pair *)
let C1092MARN_INWARD_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s /\\ %s" C1092AE_P C1092MARN_HYPS
    (c1092mppe_in 7 "&2" "&113 / &50") (c1092mppe_in 7 "&87 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MOC_CODE_CONV THEN
  let near = c1092marn_near () in
  let leftF = CONJUNCT1 (c1092moc_use C1092MPPE_WALL_AUXILIARIES) in
  let leftG = CONJUNCT1 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  let fcov = c1092mpri_useh C1092AC_NORTHWEST_F_COVER in
  let gcov = c1092mpri_useh C1092AC_NORTHWEST_G_COVER in
  let e78 = c1092moc_excl 7 8 leftF and e711 = c1092moc_excl 7 11 near
  and e78g = c1092moc_excl 7 8 leftG in
  let gtm = c1092mpri_in 7 `&87 / &50` `&2` in
  SUBGOAL_THEN gtm ASSUME_TAC THENL [MESON_TAC[gcov; e78g; e711]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let habs = mk_neg (c1092mpri_in 7 `&2` `&113 / &50`) in
  let ftm = c1092mpri_in 7 `&8 / &5` `&3` in
  SUBGOAL_THEN ftm ASSUME_TAC THENL
   [MP_TAC fcov THEN MP_TAC e78 THEN UNDISCH_TAC habs THEN MESON_TAC[]; ALL_TAC] THEN
  let t, eqs = c1092moc_layers 7 [C1092MOC_SW] in
  ACCEPT_TAC(c1092moc_apply (c1092moc_conv eqs) (SPECL t C1092MS_IMPOSSIBLE)
    [c1092moc_punit 7 t; c1092moc_pos (); c1092moc_side ();
     ASSUME gtm; ASSUME ftm; ASSUME habs; e711; e78; e78g]));;

(* Lean: PositiveInward (structure; fields side, actual, normal, positive) *)
let c1092marn_pos = new_definition
 `c1092marn_pos c1 c2 a b l (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
    (cC * cC + sC * sC = &1 /\ &0 < aC) /\
    aC = l /\
    (forall x y. linside cC sC uC vC aC x y <=>
           linside (ooc c1 c2 a b l (EL 7 c1092wc_code)) (oos c1 c2 a b l (EL 7 c1092wc_code))
                   (oou c1 c2 a b l (EL 7 c1092wc_code)) (oov c1 c2 a b l (EL 7 c1092wc_code)) l
                   (&2 - x) (&2 + y)) /\
    c977cc_normal cC sC /\
    &0 < sC`;;

(* the W-square facts shared by exists_positive and left_origin *)
let C1092MARN_W_TAC =
  let wbox = REWRITE_RULE[lcont] (c1092moc_box 8) in
  c1092marn_cf [C1092MARN_EQW] (c1092marn_win `&543 / &500` `&0`) (c1092moc_seed 8 (`&457 / &500`, `&2`)) THEN
  c1092marn_cf [C1092MARN_EQW] (c1092marn_win `&1` `&13 / &50`)
    (CONJUNCT1 (c1092moc_use C1092MPPE_WALL_AUXILIARIES)) THEN
  SUBGOAL_THEN (list_mk_forall([`x:real`; `y:real`],
                  mk_imp(c1092marn_win `x:real` `y:real`, `x <= &2`))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092MARN_EQW] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP wbox) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC (c1092moc_punit 8 C1092MARN_TW) THEN
  ASSUME_TAC (c1092moc_pos ()) THEN ASSUME_TAC (c1092moc_side ()) THEN
  SUBGOAL_THEN (list_mk_comb(`ldisj`, C1092MARN_CV @ C1092MARN_TW)) ASSUME_TAC THENL
   [REWRITE_TAC[ldisj; ASSUME C1092MARN_ACT_TM; C1092MARN_EQW] THEN REPEAT GEN_TAC THEN
    MATCH_ACCEPT_TAC (c1092moc_apart 7 8); ALL_TAC];;

(* Lean: exists_positive *)
let C1092MARN_EXISTS_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ?cC sC uC vC aC. c1092marn_pos %s cC sC uC vC aC"
    C1092AE_P C1092MARN_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let near = c1092marn_near () in
  let pair = c1092marn_use C1092MARN_INWARD_PAIR in
  let leftG = CONJUNCT1 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  let top = c1092moc_use C1092MPUO_TOP_ORIGIN in
  let center = c1092moc_use C1092MOC_BOTTOM_CENTER in
  let act = ASSUME C1092MARN_ACT_TM in
  MP_TAC(MP (SPECL C1092MARN_T7 CLF_CANONICAL_FRAME)
            (CONJ (c1092moc_punit 7 C1092MARN_T7) (c1092moc_pos ()))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cC:real` (X_CHOOSE_THEN `sC:real` (X_CHOOSE_THEN `uC:real`
    (X_CHOOSE_THEN `vC:real` (X_CHOOSE_THEN `aC:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  SUBGOAL_THEN C1092MARN_ACT_TM ASSUME_TAC THENL
   [REWRITE_TAC[GSYM C1092MARN_EQ7] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (fun th -> is_forall (concl th)));
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
      UNDISCH_TAC `abs sC <= cC` THEN UNDISCH_TAC `sC <= &0` THEN
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    c1092marn_cf [act] (c1092marn_cin `&7 / &20` `&7 / &20`) (c1092moc_seed 7 (`&33 / &20`, `&47 / &20`)) THEN
    c1092marn_cf [act] (c1092marn_cin `&0` `&13 / &50`) (CONJUNCT1 pair) THEN
    c1092marn_cf [act] (c1092marn_cin `&13 / &50` `&0`) (CONJUNCT2 pair) THEN
    c1092marn_cf [act] (mk_neg (c1092marn_cin `&0` `&0`)) (c1092moc_excl 7 5 center) THEN
    c1092marn_cf [act] (mk_neg (c1092marn_cin `&1` `&2 / &5`)) (c1092moc_excl 7 8 leftG) THEN
    c1092marn_cf [act] (mk_neg (c1092marn_cin `&13 / &50` `&1`)) (c1092moc_excl 7 11 near) THEN
    SUBGOAL_THEN (mk_forall(`x:real`, mk_imp(`&0 <= x`, mk_imp(`x <= &13 / &50`,
                    mk_neg (c1092marn_cin `x:real` `&1`))))) ASSUME_TAC THENL
     [REWRITE_TAC[act] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (list_mk_comb(`linside`, c1092moc_own 11 @ [`&2 - x`; `&3`])) ASSUME_TAC THENL
       [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&87 / &50`; `&2`] THEN
        REWRITE_TAC[near; top] THEN RASM_ARITH_TAC;
        POP_ASSUM(fun th -> ACCEPT_TAC (c1092moc_excl 7 11 th))];
      ALL_TAC] THEN
    C1092MARN_W_TAC THEN
    c1092marn_cf [C1092MARN_EQW] (c1092marn_win `&1` `&39 / &100`) (c1092moc_use C1092MARN_LEFT_TIP) THEN
    SUBGOAL_THEN (mk_binop `(<=):real->real->bool` `&0` (list_mk_comb(`lcy`, C1092MARN_TW))) ASSUME_TAC THENL
     [MP_TAC (MP (SPECL C1092MPPE_V C1092MARN_LEFT_CUT) (ASSUME C1092MOC_CTX)) THEN
      MP_TAC (c1092moc_unit 8) THEN REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING ORELSE
      (REWRITE_TAC[lcy] THEN
       SUBGOAL_THEN (mk_eq(list_mk_comb(`lcy`, C1092MARN_TW),
                           mk_binop `(-):real->real->real` (list_mk_comb(`lcy`, c1092moc_own 8)) `&2`))
         MP_TAC THENL
        [MP_TAC (c1092moc_unit 8) THEN REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING;
         MP_TAC (MP (SPECL C1092MPPE_V C1092MARN_LEFT_CUT) (ASSUME C1092MOC_CTX)) THEN
         REWRITE_TAC[lcy] THEN REAL_ARITH_TAC]);
      ALL_TAC] THEN
    MP_TAC(SPECL (C1092MARN_CV @ C1092MARN_TW) C1092SBN_IMPOSSIBLE) THEN
    ANTS_TAC THENL [C1092MARN_CLOSE_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC C1092MARN_CV THEN REWRITE_TAC[c1092marn_pos] THEN
  CONV_TAC C1092MOC_CODE_CONV THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs sC <= cC` THEN UNDISCH_TAC `&0 < sC` THEN REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* Lean: corner_halfpoint_of_missing_left_origin *)
let C1092MARN_CORNER_HALFPOINT_OF_MISSING_LEFT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ ~%s ==> %s" C1092AE_P C1092AE_HYP
    (c1092mppe_in 8 "&1" "&12 / &5") (c1092mppe_in 8 "&1" "&2") (c1092mppe_in 3 "&3 / &2" "&3")),
  REPEAT GEN_TAC THEN CONV_TAC C1092MOC_CODE_CONV THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let box8 = REWRITE_RULE[lcont] (c1092moc_box 8) and box3 = REWRITE_RULE[lcont] (c1092moc_box 3) in
  MAP_EVERY ASSUME_TAC
   [c1092moc_seed 8 (`&457 / &500`, `&2`); c1092moc_seed 3 (`&457 / &500`, `&3`);
    c1092moc_seed 3 (`&1`, `&3`); c1092moc_side (); c1092moc_pos ();
    c1092moc_punit 8 C1092MARN_TB; c1092moc_punit 3 C1092MARN_TK] THEN
  MP_TAC(SPECL (C1092MARN_TB @ C1092MARN_TK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[ldisj; C1092MARN_EQB; C1092MARN_EQK] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP box8) THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP box3) THEN REAL_ARITH_TAC;
    MATCH_ACCEPT_TAC (c1092moc_apart 3 8)]);;

(* Lean: left_origin *)
let C1092MARN_LEFT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MARN_HYPS (c1092mppe_in 8 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let near = c1092marn_near () in
  let pair = c1092marn_use C1092MARN_INWARD_PAIR in
  let leftF = CONJUNCT1 (c1092moc_use C1092MPPE_WALL_AUXILIARIES) in
  let leftG = CONJUNCT1 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  let center = c1092moc_use C1092MOC_BOTTOM_CENTER in
  let act = ASSUME C1092MARN_ACT_TM in
  let missingTm = mk_neg (c1092mpri_in 8 `&1` `&2`) in
  let half = MP (CONV_RULE C1092MOC_CODE_CONV
                  (SPECL C1092MPPE_V C1092MARN_CORNER_HALFPOINT_OF_MISSING_LEFT_ORIGIN))
                (end_itlist CONJ [ASSUME C1092MOC_NP; ASSUME C1092MOC_IMG; leftG; ASSUME missingTm]) in
  MP_TAC (c1092marn_use C1092MARN_EXISTS_POSITIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cC:real` (X_CHOOSE_THEN `sC:real` (X_CHOOSE_THEN `uC:real`
    (X_CHOOSE_THEN `vC:real` (X_CHOOSE_THEN `aC:real` MP_TAC))))) THEN
  REWRITE_TAC[c1092marn_pos] THEN CONV_TAC C1092MOC_CODE_CONV THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  CONV_TAC C1092MOC_CODE_CONV THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  ASSUME_TAC (c1092moc_side ()) THEN
  c1092marn_cf [act] (c1092marn_cin `&7 / &20` `&7 / &20`) (c1092moc_seed 7 (`&33 / &20`, `&47 / &20`)) THEN
  c1092marn_cf [act] (c1092marn_cin `&0` `&13 / &50`) (CONJUNCT1 pair) THEN
  c1092marn_cf [act] (c1092marn_cin `&13 / &50` `&0`) (CONJUNCT2 pair) THEN
  c1092marn_cf [act] (mk_neg (c1092marn_cin `&0` `&0`)) (c1092moc_excl 7 5 center) THEN
  c1092marn_cf [act] (mk_neg (c1092marn_cin `&1 / &2` `&1`)) (c1092moc_excl 7 3 half) THEN
  let outerTm = c1092mpri_in 7 `&8 / &5` `&3` in
  ASM_CASES_TAC outerTm THENL
   [c1092marn_cf [act] (c1092marn_cin `&2 / &5` `&1`) (ASSUME outerTm) THEN
    c1092marn_cf [act] (mk_neg (c1092marn_cin `&13 / &50` `&1`)) (c1092moc_excl 7 11 near) THEN
    SUBGOAL_THEN (mk_forall(`y:real`, mk_imp(`&13 / &50 <= y`, mk_imp(`y <= &2 / &5`,
                    mk_neg (c1092marn_cin `&1` `y:real`))))) ASSUME_TAC THENL
     [REWRITE_TAC[act] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (list_mk_comb(`linside`, c1092moc_own 8 @ [`&1`; `&2 + y`])) ASSUME_TAC THENL
       [MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&113 / &50`; `&12 / &5`] THEN
        REWRITE_TAC[leftF; leftG] THEN RASM_ARITH_TAC;
        POP_ASSUM(fun th -> ACCEPT_TAC (c1092moc_excl 7 8 th))];
      ALL_TAC] THEN
    MP_TAC(SPECL C1092MARN_CV C1092MIOA_POINT) THEN
    ANTS_TAC THENL [C1092MARN_CLOSE_TAC; ASM_REWRITE_TAC[]];
    c1092marn_cf [act] (mk_neg (c1092marn_cin `&2 / &5` `&1`)) (ASSUME (mk_neg outerTm)) THEN
    C1092MARN_W_TAC THEN
    c1092marn_cf [C1092MARN_EQW] (c1092marn_win `&1` `&2 / &5`) leftG THEN
    c1092marn_cf [C1092MARN_EQW] (mk_neg (c1092marn_win `&1` `&0`)) (ASSUME missingTm) THEN
    MP_TAC(SPECL (C1092MARN_CV @ C1092MARN_TW) C1092BOO_IMPOSSIBLE) THEN
    ANTS_TAC THENL [C1092MARN_CLOSE_TAC; REWRITE_TAC[]]]);;
