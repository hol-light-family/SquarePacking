(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F5TopOnlyPoints.lean.          *)
(* Original-owner point and full-profile entrance for the F5 upper-right     *)
(* ending.  Conventions of CP_OtherCases_C983_F4Filters.ml / TopOnlyPoints.ml*)
(* : owners p 3 / 6 / 10 / 11 = owner 48 / 1024 / 16384 / 32768, actual p i  *)
(* = c983e_actual c1 c2 a b l i; (owners p 6).translated 2 2 is the tuple of *)
(* C983AOP_TRANSLATE; pullX via LINSIDE_PULLX / LCONT_PULLX.                 *)
(* WallUpperMissingReach.point = WUMR_POINT, vertical_segment =              *)
(* OO_VERTICAL_SEGMENT, TopOnlyQuadrantProfile.frame / Data = OCTOQP_FRAME / *)
(* octoqp_data (the OpenSquare r is cr sr ur vr ar with unit normal and      *)
(* 0 < ar), f5_right_final / f5_final_central = C983F5RF_*, f5_top_origin =  *)
(* C983F5T_F5_TOP_ORIGIN, f5_southeast_crosspoint =                          *)
(* C983F5C_F5_SOUTHEAST_CROSSPOINT, f5_right_origin = C983WO_F5_RIGHT_ORIGIN,*)
(* northeast_left_point = C983TOP_NORTHEAST_LEFT_POINT.  Tag C983F5TOP_.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5RightFinal.ml";;
needs "n12/geometry/CP_OtherCases_C983_TopOnlyPoints.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantProfile.ml";;

let c983f5top_use th facts =
  MP (SPECL C983E_VARS th) (end_itlist CONJ ([ASSUME C983F4F_NP; ASSUME C983F4F_IMG] @ facts));;

(* Lean: right_advance_of_omitted_lower *)
let c983f5top_advance g9 noF8 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let missingF = PROVE_HYP noF8 (c983sa_missing 8 10) in
  let pR = c983fo_pull LINSIDE_PULLX 16384 in
  c983fo_apply (SPECL pR WUMR_POINT)
    [unit 16384; pos; side; MATCH_MP LCONT_PULLX (box 16384); seed 10 `&1543 / &500` `&2`;
     c983f4f_point g9; missingF; excl 16384 1024 (seed 6 `&47 / &20` `&47 / &20`)];;

let C983F5TOP_RIGHT_ADVANCE_OF_OMITTED_LOWER = c983f4f_close
  (c983sa_stmt [c983f4f_mem 19 10; mk_neg (c983f4f_mem 8 10)] (c983ab_in 16384 `&3` `&64 / &25`))
  (c983f5top_advance (ASSUME (c983f4f_mem 19 10)) (ASSUME (mk_neg (c983f4f_mem 8 10))));;

(* Lean: f5_right_bar *)
let c983f5top_bar f5 =
  let final = c983f5top_use C983F5RF_F5_RIGHT_FINAL [f5] in
  let dec tm = EQT_ELIM ((REWRITE_CONV[final; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) tm) in
  let f9 = dec (c983f4f_mem 9 10) and g9 = dec (c983f4f_mem 19 10) in
  let noF8 = dec (mk_neg (c983f4f_mem 8 10)) in
  let low = c983f4f_point f9 in
  let adv = c983f5top_advance g9 noF8 in
  let lower = `&113 / &50 <= y` and upper = `y <= &64 / &25` in
  let th = MP (SPECL (c983ab_own 16384 @ [`&3`; `&113 / &50`; `&64 / &25`; `y:real`]) OO_VERTICAL_SEGMENT)
              (end_itlist CONJ [low; adv; EQT_ELIM (REAL_RAT_REDUCE_CONV `&113 / &50 < &64 / &25`);
                                ASSUME lower; ASSUME upper]) in
  GEN `y:real` (DISCH lower (DISCH upper th));;

let C983F5TOP_F5_RIGHT_BAR = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] C983TOP_BAR) (c983f5top_bar (c983f5_f5 ()));;

(* Lean: f5_top_only_points *)
let C983F5TOP_F5_TOP_ONLY_POINTS =
  let f5 = c983f5_f5 () in
  let final = CONJUNCT1 (CONJUNCT2 (c983f5top_use C983F5RF_F5_FINAL_CENTRAL [f5])) in
  let dec tm = EQT_ELIM ((REWRITE_CONV[final; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) tm) in
  let f7 = dec (c983f4f_mem 7 6) and g7 = dec (c983f4f_mem 17 6) in
  let noF5 = c983f4f_absent 7 6 f5 in
  let top = c983f5top_use C983F5T_F5_TOP_ORIGIN [f5] in
  let bar = c983f5top_bar f5 in
  let sharp = c983f5top_use C983SA_NORTHEAST_UPPER_POINT [f7; noF5; top; bar] in
  let ext = c983f5top_use C983WO_NORTHEAST_TOP_EXTENSION
              [f7; noF5; top; c983f5top_use C983F5C_F5_SOUTHEAST_CROSSPOINT [f5]] in
  let left = c983f5top_use C983TOP_NORTHEAST_LEFT_POINT [g7; noF5; sharp; top; bar] in
  let right = c983f5top_use C983WO_F5_RIGHT_ORIGIN [f5] in
  c983f4f_close
    (c983sa_stmt [c983f4f_mem 5 7]
       (list_mk_conj [c983ab_in 1024 `&101 / &40` `&17 / &8`; c983ab_in 1024 `&5 / &2` `&3`;
                      c983ab_in 1024 `&2` `&131 / &50`; c983ab_in 16384 `&3` `&2`]))
    (end_itlist CONJ [sharp; ext; left; right]);;

(* bar (local to northeast_quadrant_profile), read through the translation by (2, 2) *)
let C983F5TOP_BAR_TRANSLATED = prove
 (`forall c s u v a. (forall z. &113 / &50 <= z ==> z <= &64 / &25 ==> ~linside c s u v a (&3) z)
     ==> forall y. &13 / &50 <= y ==> y <= &14 / &25
             ==> ~linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a (&1) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C983AOP_TRANSLATE; REAL_ARITH `&1 + &2 = &3`] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y + &2`) THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REWRITE_TAC[]);;

(* Lean: northeast_quadrant_profile *)
let C983F5TOP_NORTHEAST_QUADRANT_PROFILE =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let g7tm = c983f4f_mem 17 6 and nf5tm = mk_neg (c983f4f_mem 5 6) in
  let sharptm = c983ab_in 1024 `&101 / &40` `&17 / &8` and toptm = c983ab_in 32768 `&2` `&3` in
  let bar = ASSUME C983TOP_BAR in
  let barx =
    let lo = `&113 / &50 <= z` and hi = `z <= &64 / &25` in
    let pt = MP (MP (SPEC `z:real` bar) (ASSUME lo)) (ASSUME hi) in
    GEN `z:real` (DISCH lo (DISCH hi (excl 1024 16384 pt))) in
  let tr = c983f5rf_trans 1024 in
  let facts = [unit 1024; pos; side; seed 6 `&47 / &20` `&47 / &20`; c983f4f_point (ASSUME g7tm);
               ASSUME sharptm; PROVE_HYP (ASSUME nf5tm) (c983sa_missing 5 6);
               excl 1024 32768 (ASSUME toptm); excl 1024 48 (seed 3 `&3` `&3`);
               MP (SPECL (c983ab_own 1024) C983F5TOP_BAR_TRANSLATED) barx] in
  let frame = c983sa_apply C983F5RF_CONV (SPECL tr OCTOQP_FRAME) facts in
  let left = c983f5top_use C983TOP_NORTHEAST_LEFT_POINT
               [ASSUME g7tm; ASSUME nf5tm; ASSUME sharptm; ASSUME toptm; bar] in
  let r = [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] in
  let rin x y = list_mk_comb(`linside`, r @ [x; y]) in
  let concl0 = list_mk_exists(r, list_mk_conj
    [`cr * cr + sr * sr = &1`; `&0 < ar`; `ar = l:real`;
     list_mk_forall([`x:real`; `y:real`], mk_eq(rin `x:real` `y:real`, c983ab_in 1024 `x + &2` `y + &2`));
     list_mk_comb(`octoqp_data`, r); rin `&0` `&31 / &50`]) in
  prove(c983sa_stmt [g7tm; nf5tm; sharptm; toptm; C983TOP_BAR] concl0,
    REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    MP_TAC left THEN MP_TAC frame THEN REWRITE_TAC[C983AOP_TRANSLATE] THEN STRIP_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;
