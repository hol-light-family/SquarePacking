(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/SoutheastBranches    *)
(* .lean (namespace N12Compact.MergedPending).  Southeast branches of C683  *)
(* and C867 (the owner of mask 512).  Conventions of Families.ml /          *)
(* WallReach.ml / CentralPoints.ml: per-case theorems are OCaml lists over   *)
(* MPF_FAMILIES (c683, c700, c867); every statement keeps the hypothesis     *)
(* 512 IN family k (vacuous for c700), further Lean hypotheses (inward,      *)
(* missing) are added to the antecedent conjunction.  ElbowPoint.points_     *)
(* original = OCEP_POINTS_ORIGINAL, CrossedElbow.impossible_original =       *)
(* OCCE_IMPOSSIBLE_ORIGINAL, OutwardPoint.point_original =                   *)
(* CCOP_POINT_ORIGINAL, OutwardBarPoint.point_original =                     *)
(* OCOBP_POINT_ORIGINAL, C981CompletionOutwardAnchor.nonnegative_impossible  *)
(* = C981OA_NONNEGATIVE_IMPOSSIBLE, ClosedFrames.canonical_frame =           *)
(* CLF_CANONICAL_FRAME.  "?B : OpenSquare" is an existential over a 5-tuple  *)
(* with its OpenSquare invariants (c*c+s*s = 1, 0 < side).  Tag MPSE_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_CentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;

(* the two outward points on pullY W (local form of southeast_outward_points' last step) *)
let MPSE_RAW_OUTWARD = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\ linside c s u v a (&3) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\ ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&3) (&1) /\ ~linside c s u v a (&1543 / &500) (&1) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a z (&1))
     ==> linside c s u v a (&123 / &50) (&201 / &100) /\
         linside c s u v a (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th ->
    MP_TAC(SPECL [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`] th) THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; FIRST_ASSUM MATCH_ACCEPT_TAC; RASM_ARITH_TAC;
             UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC];
      DISCH_TAC]) [CCOP_POINT_ORIGINAL; OCOBP_POINT_ORIGINAL] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Packing level.                                                            *)
(* ------------------------------------------------------------------------- *)

let mpse_inst_member fam th =
  MP (SPECL MPWR_VARS th) (CONJ (mpwr_np fam) (CONJ (CONJUNCT2 (ASSUME (mpwr_hyp fam))) (in_fam 512 fam)));;
(* |- !c1 .. l. NPACK .. /\ IMAGE .. = fam /\ 512 IN fam [/\ extra] ==> body *)
let mpse_stmt fam extra body =
  list_mk_forall(MPWR_VARS, mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`;
    mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam);
    mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `512`), fam)] @ extra), body));;
(* per case: vacuous for c700, otherwise from the theorem proved under NPACK /\ IMAGE = fam *)
let mpse_case extra body mk = map (fun fam ->
  let tm = mpse_stmt fam extra body in
  if rhs (concl (in_fam_conv 512 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 512 fam]) else
  let th = mk fam in
  prove (tm, REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[])) MPF_FAMILIES;;
let mpse_prove fam extra body tac =
  prove(mpwr_stmt fam (if extra = [] then body else mk_imp(list_mk_conj extra, body)),
        REPEAT GEN_TAC THEN DISCH_TAC THEN tac);;
let mpse_unit fam m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) (mpwr_np fam);;
let mpse_side fam = MP (SPECL MPWR_VARS OO_SIDE) (mpwr_np fam);;
let mpse_pos fam = MP (REAL_ARITH `&1 < l ==> &0 < l`) (mpse_side fam);;
let mpse_some_tac fam m k excls =
  let np = mpwr_np fam and img = CONJUNCT2 (ASSUME (mpwr_hyp fam)) in
  let kl = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let ord = EQF_ELIM (AUXEX_CONV (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral m),
                                          mk_comb(`auxex`, mk_small_numeral k)))) in
  let some = MP (SPECL (MPWR_VARS @ [fam; mk_small_numeral m; mk_small_numeral k]) MPCP_SOME_AUXILIARY)
               (end_itlist CONJ [np; img; in_fam m fam; kl; ord]) in
  MP_TAC some THEN DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MPCP_ENUM_TAC `j:num` 10 THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV THENC
                     REWRITE_CONV[VECTOR_2] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  REWRITE_TAC excls THEN TRY(DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let mpse_tm m x y = mpwr_inside m x y;;

(* Lean: southeast_marker (private) *)
let MPSE_SOUTHEAST_MARKER = mpse_case [] (mpse_tm 512 `&47 / &20` `&33 / &20`) (fun fam ->
  mpwr_prove fam (mpse_tm 512 `&47 / &20` `&33 / &20`) (mpwr_seed fam 512 (`&47 / &20`, `&33 / &20`)));;
let mpse_marker fam = mpwr_seed fam 512 (`&47 / &20`, `&33 / &20`);;

(* Lean: southeast_f8 (private) *)
let mpse_f8 fam = mpwr_auxpt 512 8 (mpse_inst_member fam (el (index fam MPF_FAMILIES) MPD_SOUTHEAST_LOWER));;
let MPSE_SOUTHEAST_F8 = mpse_case [] (mpse_tm 512 `&3` `&87 / &50`) (fun fam ->
  mpwr_prove fam (mpse_tm 512 `&3` `&87 / &50`) (mpcp_norm (mpse_f8 fam)));;

(* Lean: southeast_bottom (private) *)
let MPSE_BOTTOM_BODY = mk_forall(`x:real`, mk_imp(`&113 / &50 <= x`, mk_imp(`x <= &14 / &5`,
  mk_neg (mpse_tm 512 `x:real` `&1`))));;
let mpse_bottom fam =
  let reach = CONJUNCT2 (mpwr_inst fam (el (index fam MPF_FAMILIES) MPWR_BOTTOM_REACH)) in
  let ap = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam 512 8192)) in
  let x = `x:real` in
  let r = UNDISCH (UNDISCH (REWRITE_RULE[IMP_CONJ] (SPEC x reach))) in
  let n = REWRITE_RULE[r] (SPECL [x; `&1`] ap) in
  GEN x (DISCH `&113 / &50 <= x` (DISCH `x <= &14 / &5` n));;
let MPSE_SOUTHEAST_BOTTOM = mpse_case [] MPSE_BOTTOM_BODY (fun fam ->
  mpwr_prove fam MPSE_BOTTOM_BODY (mpse_bottom fam));;

(* Lean: southeast_g_cover *)
let MPSE_G_COVER_BODY = mk_disj(mpse_tm 512 `&113 / &50` `&2`, mpse_tm 512 `&3` `&8 / &5`);;
let mpse_g_cover fam =
  let i = index fam MPF_FAMILIES in
  let lab = mpwr_labels fam and w = mpcp_walls fam in
  let right = if i = 0 then mpcp_excl fam 512 32 (mpwr_bar (mpwr_inst fam MPF_C683_RIGHT_SINGLETON) (snd (mpcp_pt 1 9)))
              else mpcp_label fam 512 16384 19 (CONJUNCT2 (mpwr_inst fam MPD_C867_RIGHT_LABELS)) in
  let excls =
    [mpcp_wall_y fam 512 2 (el 1 w) 0 1;
     mpcp_label fam 512 4096 11 (el 3 lab);
     mpcp_wall_x fam 512 1 (el 0 w) 2 1;
     mpcp_label fam 512 256 13 (el 1 lab);
     mpcp_label fam 512 32768 14 (el 7 lab);
     mpcp_label fam 512 8192 15 (el 5 lab);
     mpcp_wall_x fam 512 16 (el 2 w) 7 1;
     right] in
  UNDISCH (SPEC_ALL (mpse_prove fam [] MPSE_G_COVER_BODY (mpse_some_tac fam 512 1 excls)));;
let MPSE_SOUTHEAST_G_COVER = mpse_case [] MPSE_G_COVER_BODY (fun fam ->
  mpwr_prove fam MPSE_G_COVER_BODY (mpse_g_cover fam));;

(* Lean: southeast_g8 *)
let mpse_g8 fam =
  let i = index fam MPF_FAMILIES in
  let half = CONJUNCT1 (mpwr_inst fam (el i MPCP_SOUTHWEST_CROSSPOINTS)) in
  let facts = map mpcp_norm
    [mpse_unit fam 512; mpse_side fam; mpse_marker fam; mpse_f8 fam;
     mpwr_missing fam 512 10; mpwr_missing fam 512 14; mpwr_excl fam 512 256 half] in
  let th = mpse_prove fam [] (mpse_tm 512 `&3` `&8 / &5`)
    (MP_TAC (mpse_g_cover fam) THEN
     MP_TAC(SPECL (butlast (mpwr_tuple 512) @ [`l:real`]) OCEP_POINTS_ORIGINAL) THEN
     REWRITE_TAC facts THEN CONV_TAC TAUT) in
  UNDISCH (SPEC_ALL th);;
let MPSE_SOUTHEAST_G8 = mpse_case [] (mpse_tm 512 `&3` `&8 / &5`) (fun fam ->
  mpwr_prove fam (mpse_tm 512 `&3` `&8 / &5`) (mpse_g8 fam));;

(* Lean: southeast_right_crosspoint *)
let MPSE_SOUTHEAST_RIGHT_CROSSPOINT =
  let inward = mpse_tm 512 `&113 / &50` `&2` in
  mpse_case [inward] (mpse_tm 512 `&5 / &2` `&2`) (fun fam ->
    let i = index fam MPF_FAMILIES in
    let half = CONJUNCT1 (mpwr_inst fam (el i MPCP_SOUTHWEST_CROSSPOINTS)) in
    let bottom = MP (MP (SPEC `&14 / &5` (mpse_bottom fam))
                    (EQT_ELIM (REAL_RAT_REDUCE_CONV `&113 / &50 <= &14 / &5`))) (SPEC `&14 / &5` REAL_LE_REFL) in
    let facts = map mpcp_norm
      [mpse_unit fam 512; mpse_side fam; mpse_pos fam; mpse_marker fam; mpse_f8 fam;
       mpwr_excl fam 512 256 half; bottom] in
    mpse_prove fam [inward] (mpse_tm 512 `&5 / &2` `&2`)
      (DISCH_TAC THEN
       MP_TAC(SPECL (butlast (mpwr_tuple 512) @ [`l:real`; `&4 / &5`]) OCCE_IMPOSSIBLE_ORIGINAL) THEN
       CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
       ASM_REWRITE_TAC facts THEN CONV_TAC TAUT));;

(* Lean: southeast_outward_frame *)
let MPSE_FRAME_BODY =
  let t = butlast (mpwr_tuple 512) in
  let ex = `exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
              &0 < c' /\ s' < &0 /\ --s' <= c' /\ a' = l /\
              (forall x y. linside c' s' u' v' a' x y <=> linside cO sO uO vO l x y)` in
  subst (zip t [`cO:real`; `sO:real`; `uO:real`; `vO:real`]) ex;;
let MPSE_SOUTHEAST_OUTWARD_FRAME =
  let missing = mk_neg (mpse_tm 512 `&113 / &50` `&2`) in
  mpse_case [missing] MPSE_FRAME_BODY (fun fam ->
    let corner = mpwr_excl fam 512 12 (mpwr_seed fam 12 (`&3`, `&1`)) in
    let facts = map mpcp_norm
      [mpse_marker fam; mpse_g8 fam; corner; mpwr_missing fam 512 14] @ [mpse_bottom fam] in
    let t = butlast (mpwr_tuple 512) in
    mpse_prove fam [missing] MPSE_FRAME_BODY
      (DISCH_TAC THEN
       MP_TAC(SPECL (t @ [`l:real`]) CLF_CANONICAL_FRAME) THEN
       ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC (mpse_unit fam 512); ACCEPT_TAC (mpse_pos fam)]; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
         (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
       FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = l`)) THEN
       MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `l:real`] THEN
       ASM_REWRITE_TAC[] THEN
       ASM_CASES_TAC `&0 <= s'` THENL
        [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `l:real`] C981OA_NONNEGATIVE_IMPOSSIBLE) THEN
         ANTS_TAC THENL
          [REPEAT CONJ_TAC THEN
           FIRST [ASM_REWRITE_TAC facts THEN NO_TAC; RASM_ARITH_TAC;
                  MP_TAC (mpse_side fam) THEN REAL_ARITH_TAC;
                  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real` THEN STRIP_TAC THEN
                  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (mpse_bottom fam)) THEN ASM_REWRITE_TAC[]];
           REWRITE_TAC[]];
         RASM_ARITH_TAC]));;

(* Lean: southeast_outward_points *)
let MPSE_OUTWARD_BODY = mk_conj(mpse_tm 512 `&123 / &50` `&201 / &100`, mpse_tm 512 `&101 / &40` `&17 / &8`);;
let MPSE_SOUTHEAST_OUTWARD_POINTS =
  let missing = mk_neg (mpse_tm 512 `&113 / &50` `&2`) in
  mpse_case [missing] MPSE_OUTWARD_BODY (fun fam ->
    let corner p = mpcp_norm (mpwr_excl fam 512 12 (mpwr_seed fam 12 p)) in
    let facts = map mpcp_norm
      [mpse_unit fam 512; mpse_side fam; mpse_marker fam; mpse_f8 fam; mpse_g8 fam;
       mpwr_missing fam 512 14; corner (`&3`, `&1`); corner (`&1543 / &500`, `&1`); mpse_bottom fam] in
    mpse_prove fam [missing] MPSE_OUTWARD_BODY
      (DISCH_TAC THEN MATCH_MP_TAC MPSE_RAW_OUTWARD THEN REPEAT CONJ_TAC THEN
       FIRST (FIRST_ASSUM ACCEPT_TAC :: map MATCH_ACCEPT_TAC facts)));;
