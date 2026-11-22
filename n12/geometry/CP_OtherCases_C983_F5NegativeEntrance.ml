(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F5NegativeEntrance.lean        *)
(* (N12Compact.Completion.OtherCases.C983).  Full original-owner entrance    *)
(* for the last negative southeast/right triple (actual frames and faces;    *)
(* not the three-square ending).  Conventions of                             *)
(* CP_OtherCases_C983_F5NegativeFrame.ml: owners p 5 / 6 / 7 / 9 / 10 =      *)
(* owner 512 / 1024 / 2304 / 8192 / 16384.  NegativeTripleFaces.Data /       *)
(* faces = ccntf_data / CCNTF_FACES, TopOnlyQuadrantProfile.Data =           *)
(* octoqp_data, northeast_quadrant_profile                                   *)
(* C983F5TOP_NORTHEAST_QUADRANT_PROFILE, f5_negative_frame                   *)
(* C983FNF_F5_NEGATIVE_FRAME, f5_final_central C983F5RF_F5_FINAL_CENTRAL,    *)
(* absent_of_foreign c983f4f_absent, f5_top_only_points                      *)
(* C983F5TOP_F5_TOP_ONLY_POINTS, f5_top_origin C983F5T_F5_TOP_ORIGIN,        *)
(* f5_right_bar C983F5TOP_F5_RIGHT_BAR, f5_merged_center                     *)
(* C983MCF_F5_MERGED_CENTER, bottom_bar C983AB_BOTTOM_BAR.  The existential  *)
(* squares E N carry their OpenSquare invariants.  Tag C983FNE_.             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5NegativeFrame.ml";;
needs "n12/geometry/CP_OtherCases_NegativeTripleFaces.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantScalars.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantProfile.ml";;

let C983FNE_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let C983FNE_N = [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`];;

(* Lean: f5_negative_entrance *)
let C983FNE_F5_NEGATIVE_ENTRANCE =
  let f5tm = c983f4f_mem 5 7 in
  let xv = `x:real` and yv = `y:real` in
  let plus2 t = mk_binop `(+):real->real->real` t `&2` in
  let inq q x y = list_mk_comb(`linside`, q @ [x; y]) in
  let iffq q m = list_mk_forall([xv; yv], mk_iff(inq q xv yv, c983ab_in m (plus2 xv) (plus2 yv))) in
  let concl = list_mk_exists(C983FNE_E @ C983FNE_N, list_mk_conj
    [`cE * cE + sE * sE = &1`; `&0 < aE`; `cr * cr + sr * sr = &1`; `&0 < ar`;
     `aE:real = l`; `ar:real = l`; iffq C983FNE_E 512; iffq C983FNE_N 1024;
     `ccntf_data cE sE uE vE aE (--sE)`; `octoqp_data cr sr ur vr ar`;
     inq C983FNE_N `&0` `&31 / &50`; inq C983FNE_N `&1 / &2` `&1`]) in
  prove
   (c983sa_stmt [f5tm] concl,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    let f5 = ASSUME f5tm in
    let frame = c983f5_use C983FNF_F5_NEGATIVE_FRAME [f5] in
    let final = c983f5_use C983F5RF_F5_FINAL_CENTRAL [f5] in
    let dec eq tm = EQT_ELIM ((REWRITE_CONV[eq; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) tm) in
    let g7 = dec (CONJUNCT1 (CONJUNCT2 final)) (c983f4f_mem 17 6) in
    let noF5 = c983f4f_absent 7 6 f5 in
    let points = c983f5_use C983F5TOP_F5_TOP_ONLY_POINTS [f5] in
    let nq = c983f5_use C983F5TOP_NORTHEAST_QUADRANT_PROFILE
               [g7; noF5; CONJUNCT1 points; c983f5_use C983F5T_F5_TOP_ORIGIN [f5];
                c983f5_use C983F5TOP_F5_RIGHT_BAR [f5]] in
    let iffE = ASSUME (iffq C983FNE_E 512) and iffN = ASSUME (iffq C983FNE_N 1024) in
    let rr = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) in
    let toQ iff th x y = EQ_MP (SYM (rr (SPECL [x; y] iff))) th in
    let notQ iff th x y = EQ_MP (SYM (AP_TERM `~` (rr (SPECL [x; y] iff)))) th in
    let marker = toQ iffE (seed 5 `&47 / &20` `&33 / &20`) `&7 / &20` `--(&7 / &20)` in
    let elbow = toQ iffE (c983f4f_point (c983f5_use C983F5_F5_SOUTHEAST_G6 [f5])) `&13 / &50` `&0` in
    let missingCenter = notQ iffE (excl 512 2304 (c983f5_use C983MCF_F5_MERGED_CENTER [f5])) `&0` `&0` in
    let missingOrigin = notQ iffE (excl 512 16384 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 points)))) `&1` `&0` in
    let missingSharp = notQ iffE (excl 512 1024 (CONJUNCT1 points)) `&21 / &40` `&1 / &8` in
    let nTop = toQ iffN (CONJUNCT1 (CONJUNCT2 points)) `&1 / &2` `&1` in
    let fneBottomBar = REWRITE_RULE[IMP_IMP] (MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ())) in
    let a512_8192 = apart 512 8192 in
    MP_TAC frame THEN MP_TAC nq THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC C983FNE_N THEN STRIP_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C983FNE_E THEN STRIP_TAC THEN
    SUBGOAL_THEN `forall x. &13 / &50 <= x /\ x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))` ASSUME_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REWRITE_TAC[iffE] THEN DISCH_TAC THEN
      SUBGOAL_THEN (c983ab_in 8192 `x + &2` `--(&1) + &2`) ASSUME_TAC THENL
       [CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN MATCH_MP_TAC fneBottomBar THEN RASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`x + &2`; `--(&1) + &2`] a512_8192) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY ASSUME_TAC [marker; elbow; missingCenter; missingOrigin; missingSharp; nTop] THEN
    SUBGOAL_THEN `ccntf_data cE sE uE vE aE (--sE)` ASSUME_TAC THENL
     [MATCH_MP_TAC CCNTF_FACES THEN REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; MP_TAC side THEN RASM_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC (C983FNE_E @ C983FNE_N) THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC);;
