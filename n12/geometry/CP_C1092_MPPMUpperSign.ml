(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMUpperSign.lean                       *)
(* (N12Compact.C1092MPPMUpperSign).  The actual northeast sign and initial   *)
(* four-face table in the normalized MPPM one-omission entrance.             *)
(* Conventions and forward toolkit of CP_C1092_MPPMOmissionCenter.ml         *)
(* (c1092moc_ functions; owners p i at mask EL i c1092wc_code, side l;       *)
(* WallContext p mppm is c1092wc_ctx c1 c2 a b l c1092mppe_mppm; omitted is  *)
(* C1092MPPE_OMIT).  The private side_gt / side_same / marker_point are      *)
(* C1092MOC_SIDE_GT / C1092MOC_SIDE_SAME / C1092MOC_MARKER_POINT.            *)
(* PositiveActual p N is c1092mpus_pos c1 c2 a b l cN sN uN vN aN (with the  *)
(* OpenSquare invariants); Faces N is c1092mpus_faces.  translate /          *)
(* pullSwap / clockwise: C1092RC_INSIDE_TRANSLATE / LINSIDE_PULLSW /         *)
(* C1092MEA_INSIDE_CLOCKWISE; canonical_frame CLF_CANONICAL_FRAME;           *)
(* C1092MMMPNortheastSign.positive C1092MNSG_POSITIVE; MPPMPointCore.        *)
(* rectangle C1092MPC_RECTANGLE; MPPMTopOrigin.right_origin                  *)
(* C1092MTO_RIGHT_ORIGIN; MPPMOmissions.at_most_one C1092MOM_AT_MOST_ONE;    *)
(* TopOnlyLeftPoint.positive_faces OCTOLP_POSITIVE_FACES; SharpPointScalars. *)
(* half_lower OCSPS_HALF_LOWER.  Tag C1092MPUS_.                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMPointCore.ml";;
needs "n12/geometry/CP_C1092_MPPMTopOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMOmissions.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: PositiveActual (structure; fields side, actual, normal, positive) *)
let c1092mpus_pos = new_definition
 `c1092mpus_pos c1 c2 a b l (cN:real) (sN:real) (uN:real) (vN:real) (aN:real) <=>
    (cN * cN + sN * sN = &1 /\ &0 < aN) /\
    aN = l /\
    (forall x y. linside cN sN uN vN aN x y <=>
           linside (ooc c1 c2 a b l (EL 6 c1092wc_code)) (oos c1 c2 a b l (EL 6 c1092wc_code))
                   (oou c1 c2 a b l (EL 6 c1092wc_code)) (oov c1 c2 a b l (EL 6 c1092wc_code)) l
                   (&2 + y) (&2 + x)) /\
    c977cc_normal cN sN /\
    &0 < sN`;;

let C1092MPUS_HYPS = Printf.sprintf "%s /\\ %s /\\ %s" C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT;;

(* linside instance of a ranged packing theorem at literal arguments *)
let c1092mpus_at th args =
  REWRITE_RULE[] (CONV_RULE (DEPTH_CONV REAL_RAT_LE_CONV) (SPECL args (c1092moc_use th)));;
let c1092mpus_core x y = c1092mpus_at C1092MPC_RECTANGLE [x; y];;

let C1092MPUS_CW = (C1092MEA_INSIDE_CLOCKWISE, ([]:term list));;

(* Lean: exists_positive *)
let C1092MPUS_EXISTS_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ?cN sN uN vN aN. c1092mpus_pos %s cN sN uN vN aN"
    C1092AE_P C1092MPUS_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let tq, eqq = c1092moc_layers 6 [C1092MOC_SW; c1092moc_tr `&2` `&2`] in
  let tC, eqC = c1092moc_layers 5 [C1092MOC_SW; c1092moc_tr `&2` `&2`; C1092MPUS_CW] in
  let tN = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] in
  let tB = [`cN:real`; `sN:real`; `--vN - aN`; `uN:real`; `aN:real`] in
  let eqB = GENL [`x:real`; `y:real`] (SPECL (tN @ [`x:real`; `y:real`]) C1092MEA_INSIDE_CLOCKWISE) in
  let pair = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let m4 = c1092moc_seed 4 (`&33 / &20`, `&33 / &20`)
  and m5 = c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)
  and m6 = c1092moc_seed 6 (`&47 / &20`, `&47 / &20`) in
  let bottomTip = c1092mpus_at C1092MPPE_OMITTED_BOTTOM_BAR [`&239 / &100`] in
  let topTip = c1092moc_use C1092MPPE_TOP_TIP in
  let facts = [c1092moc_punit 5 tC; c1092moc_pos (); c1092moc_side ();
               c1092mpus_core `&2` `&2`; c1092mpus_core `&5 / &2` `&2`; c1092mpus_core `&2` `&3 / &2`;
               m5; c1092moc_excl 5 4 m4; c1092moc_excl 5 6 m6; c1092moc_excl 5 9 bottomTip;
               m6; CONJUNCT1 pair; CONJUNCT2 pair;
               c1092moc_excl 6 5 (c1092mpus_core `&239 / &100` `&2`);
               c1092moc_excl 6 11 topTip;
               c1092moc_excl 6 10 (c1092moc_seed 10 (`&1543 / &500`, `&2`));
               c1092moc_excl 6 2 (c1092moc_seed 2 (`&3`, `&3`));
               c1092moc_excl 6 5 (c1092mpus_core `&5 / &2` `&2`);
               c1092moc_apart 5 6] in
  MP_TAC(MP (SPECL tq CLF_CANONICAL_FRAME) (CONJ (c1092moc_punit 6 tq) (c1092moc_pos ()))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(fun equiv -> if is_forall (concl equiv) &&
      (match strip_comb (lhs (snd (strip_forall (concl equiv)))) with (f, args) ->
         f = `linside` && el 0 args = `cN:real`) then
   (SUBGOAL_THEN `&0 < sN` ASSUME_TAC THENL
     [MP_TAC(SPECL (tC @ tB) C1092MNSG_POSITIVE) THEN
      REWRITE_TAC[ldisj] THEN CONV_TAC (c1092moc_conv (eqC @ [eqB; equiv] @ eqq)) THEN
      ANTS_TAC THENL
       [MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM (ACCEPT_TAC o SYM);
               REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC tN THEN REWRITE_TAC[c1092mpus_pos] THEN
    CONV_TAC C1092MOC_CODE_CONV THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC[equiv] THEN REWRITE_TAC (map (fun e -> SPEC_ALL e) eqq) THEN
      REWRITE_TAC[REAL_ARITH `forall x. x + &2 = &2 + x`];
      REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs sN <= cN` THEN UNDISCH_TAC `&0 < sN` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC])
    else NO_TAC));;

(* Lean: Faces (structure) *)
let c1092mpus_faces = new_definition
 `c1092mpus_faces (c:real) s u v a <=>
    (&2 / &5) * s <= u /\ (&2 / &5) * c - s <= v /\
    u + a <= c + s /\ v + a <= c /\
    (&1 + c) / &4 < s`;;

(* the fourth ordinary point is owned once the bottom one is omitted *)
let C1092MPUS_TOPF = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MPUS_HYPS
    (c1092mppe_in 11 "&12 / &5" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`1`; `3`]) C1092MOM_AT_MOST_ONE) THEN
  ASM_REWRITE_TAC[c1092mom_missing; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092MOM_OPOINT_ELS) THEN
  REWRITE_TAC[FST; SND] THEN
  ASM_REWRITE_TAC[]);;

(* an N-fact from an owner-6 fact through the actual chart *)
let C1092MPUS_N_TAC th tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_ASSUM(fun e -> if is_forall(concl e) && is_iff(snd(strip_forall(concl e)))
                         then REWRITE_TAC[e] else NO_TAC) THEN
    CONV_TAC C1092MOC_CODE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ACCEPT_TAC th;
    ALL_TAC];;

(* Lean: faces *)
let C1092MPUS_FACES = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ c1092mpus_pos %s cN sN uN vN aN
      ==> c1092mpus_faces cN sN uN vN aN" C1092AE_P C1092MPUS_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mpus_pos] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cN sN`)) THEN
  ASSUME_TAC(c1092moc_side ()) THEN
  let pair = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let wa = c1092moc_use C1092MPPE_WALL_AUXILIARIES in
  let topF = c1092moc_use C1092MPUS_TOPF in
  let nin x y = list_mk_comb(`linside cN sN uN vN l`, [x; y]) in
  C1092MPUS_N_TAC (c1092moc_seed 6 (`&47 / &20`, `&47 / &20`)) (nin `&7 / &20` `&7 / &20`) THEN
  C1092MPUS_N_TAC (CONJUNCT1 pair) (nin `&13 / &50` `&1`) THEN
  C1092MPUS_N_TAC (c1092moc_excl 6 5 (c1092mpus_core `&113 / &50` `&2`)) (mk_neg(nin `&0` `&13 / &50`)) THEN
  C1092MPUS_N_TAC (c1092moc_excl 6 10 (c1092moc_use C1092MTO_RIGHT_ORIGIN)) (mk_neg(nin `&0` `&1`)) THEN
  C1092MPUS_N_TAC (c1092moc_excl 6 2 (c1092moc_seed 2 (`&3`, `&3`))) (mk_neg(nin `&1` `&1`)) THEN
  C1092MPUS_N_TAC (c1092moc_excl 6 11 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 wa)))) (mk_neg(nin `&1` `&13 / &50`)) THEN
  C1092MPUS_N_TAC (c1092moc_excl 6 5 (c1092mpus_core `&12 / &5` `&2`)) (mk_neg(nin `&0` `&2 / &5`)) THEN
  C1092MPUS_N_TAC (c1092moc_excl 6 11 topF) (mk_neg(nin `&1` `&2 / &5`)) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `l:real`] OCTOLP_POSITIVE_FACES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&7 / &10 <= cN`; `&0 < l`] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th)))) THEN
  OCTOLP_STEP `(&2 / &5) * sN <= uN` [mk_neg(nin `&0` `&2 / &5`)] THEN
  OCTOLP_STEP `(&2 / &5) * cN - sN <= vN` [mk_neg(nin `&1` `&2 / &5`)] THEN
  SUBGOAL_THEN `&1 < (&3 / &5) * cN + sN` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&2 / &5) * cN - sN <= vN`; `vN + l <= cN`; `&1 < l`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + cN < &4 * sN` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cN:real`; `sN:real`; `&3 / &5`] OCSPS_HALF_LOWER) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN ANTS_TAC THENL
     [UNDISCH_TAC `&7 / &10 <= cN` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `sN / (&1 + cN) * (&1 + cN) = sN` MP_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN UNDISCH_TAC `&7 / &10 <= cN` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`sN / (&1 + cN)`, `h:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &4 < h` ASSUME_TAC THENL
     [UNDISCH_TAC `&1 - &3 / &5 < (&1 + &3 / &5) * h` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (h - &1 / &4) * (&1 + cN)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      MAP_EVERY UNDISCH_TAC [`&1 / &4 < h`; `&7 / &10 <= cN`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `h * (&1 + cN) = sN` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mpus_faces] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&1 + cN < &4 * sN` THEN REAL_ARITH_TAC);;
