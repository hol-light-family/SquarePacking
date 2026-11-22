(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualProfiles.lean                  *)
(* (N12Compact.C1092MPPMActualProfiles).  Actual MPPM one-omission E/N/R     *)
(* inputs for the common two-fifths ending.  (Lean header: "Source only,     *)
(* uncompiled".)  Conventions and forward toolkit of                         *)
(* CP_C1092_MPPMOmissionCenter.ml (c1092moc_*; owners p i at mask EL i       *)
(* c1092wc_code, side l; WallContext p mppm is C1092MPPE_CTX, omitted is     *)
(* C1092MPPE_OMIT, near is C1092MARN_NEAR).  side_gt / side_same / mark      *)
(* (private) are OO_SIDE / l = l / oo_seed markers.                          *)
(* MPPMUpperSign.PositiveActual p N is c1092mpus_pos .. cN sN uN vN aN;      *)
(* NortheastCore = c1092mtfen_core, northeast_faces C1092MTFEN_NORTHEAST_     *)
(* FACES; PointCore.rectangle via c1092mpus_core; omitted_bottom_neighbors   *)
(* C1092MPPE_OMITTED_BOTTOM_NEIGHBORS; TopOrigin.right_origin                *)
(* C1092MTO_RIGHT_ORIGIN; wall_auxiliaries C1092MPPE_WALL_AUXILIARIES;       *)
(* RightInner.other_ordinary C1092MPRI_OTHER_ORDINARY; ActualRightNear.      *)
(* exists_positive / inward_pair / left_origin (PositiveInward =             *)
(* c1092marn_pos) C1092MARN_*; OmissionCenter.bottom_center                  *)
(* C1092MOC_BOTTOM_CENTER; the floor lemmas C1092MTFF_*;                     *)
(* PositiveInwardHalfangle.small_angle_of_bar C1092MPIH_SMALL_ANGLE_OF_BAR;  *)
(* C1092TwoFifths.Southeast / Right = C1092TF_southeast / C1092TF_right.     *)
(* SoutheastActual p E is c1092mpap_actual (E's OpenSquare invariants as     *)
(* explicit conjuncts of the existential).  clockwise^3 C is the tuple       *)
(* (c, s, v, --u - a, a) (C1092MTFES_INVERSE_INSIDE); (pullSwap q).translated*)
(* 2 2 is c1092moc_layers [C1092MOC_SW; tr 2 2].  Tag C1092MPAP_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualRightNear.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNortheast.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceFloor.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceSoutheast.ml";;
needs "n12/geometry/CP_C1092_MPPMUpperSign.ml";;
needs "n12/geometry/CP_C1092_MPPMTopOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMRightInner.ml";;
needs "n12/geometry/CP_C1092_MPPMOmissionCenter.ml";;
needs "n12/geometry/CP_C1092_MMMP_PositiveInwardHalfangle.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsData.ml";;

(* Lean: northeast_core *)
let C1092MPAP_NORTHEAST_CORE = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ c1092mpus_pos %s cN sN uN vN aN
      ==> c1092mtfen_core cN sN uN vN aN" C1092AE_P C1092MPUS_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mpus_pos] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cN sN`)) THEN
  MATCH_MP_TAC C1092MTFEN_NORTHEAST_FACES THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MOC_CODE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let pair = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let wa = c1092moc_use C1092MPPE_WALL_AUXILIARIES in
  let oo = c1092moc_use C1092MPRI_OTHER_ORDINARY in
  REWRITE_TAC[c1092moc_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 pair; CONJUNCT2 pair;
    c1092moc_excl 6 5 (c1092mpus_core `&113 / &50` `&2`);
    c1092moc_excl 6 5 (c1092mpus_core `&12 / &5` `&2`);
    c1092moc_excl 6 10 (c1092moc_use C1092MTO_RIGHT_ORIGIN);
    c1092moc_excl 6 2 (c1092moc_seed 2 (`&3`, `&3`));
    c1092moc_excl 6 11 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 wa)));
    c1092moc_excl 6 11 (CONJUNCT2 oo)] THEN
  MP_TAC(c1092moc_side ()) THEN UNDISCH_TAC `&0 < sN` THEN UNDISCH_TAC `sN <= cN` THEN
  UNDISCH_TAC `&7 / &10 <= cN` THEN REAL_ARITH_TAC);;

(* Lean: SoutheastActual (structure) *)
let c1092mpap_actual = new_definition
 `c1092mpap_actual (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                   (cE:real) (sE:real) (uE:real) (vE:real) (aE:real) <=>
    aE = l /\
    (forall x y. linside cE sE uE vE aE x y <=>
           linside (ooc c1 c2 a b l (EL 7 c1092wc_code)) (oos c1 c2 a b l (EL 7 c1092wc_code))
                   (oou c1 c2 a b l (EL 7 c1092wc_code)) (oov c1 c2 a b l (EL 7 c1092wc_code)) l
                   (&2 + y) (&2 + x)) /\
    c977cc_normal cE sE /\ &0 < sE`;;

(* clockwise^3 of a positive inward C is a SoutheastActual square *)
let C1092MPAP_INVERSE_ACTUAL = prove
 (`forall c1 c2 a b l cC sC uC vC aC.
     c1092marn_pos c1 c2 a b l cC sC uC vC aC
     ==> c1092mpap_actual c1 c2 a b l cC sC vC (--uC - aC) aC`,
  REWRITE_TAC[c1092marn_pos; c1092mpap_actual; C1092MTFES_INVERSE_INSIDE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&2 - --x = &2 + x`]);;

(* (pullSwap (owners p i)).translated 2 2 and its plain equivalence *)
let c1092mpap_swtr i =
  let t = fst (c1092moc_layers i [C1092MOC_SW; c1092moc_tr `&2` `&2`]) in
  let x = `x:real` and y = `y:real` in
  t, prove(list_mk_forall([x; y], mk_eq(list_mk_comb(`linside`, t @ [x; y]),
                                       list_mk_comb(`linside`, c1092moc_own i @ [`&2 + y`; `&2 + x`]))),
           REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092MPAP_HYPS = C1092MARN_HYPS;;

(* the bottom bar of owner 8: (1, 2 + x) for 0 <= x <= 2/5 *)
let C1092MPAP_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s ==> !x. &0 <= x /\\ x <= &2 / &5 ==> %s"
    C1092AE_P C1092MPAP_HYPS (c1092mppe_in 8 "&1" "&2 + x")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V C1092MARN_LEFT_ORIGIN) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPRI_OTHER_ORDINARY) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&2`; `&12 / &5`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 <= x`; `x <= &2 / &5`] THEN REAL_ARITH_TAC);;

(* Lean: southeast_profile *)
let C1092MPAP_SOUTHEAST_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ c1092mpus_pos %s cN sN uN vN aN
      ==> ?cE sE uE vE aE. cE * cE + sE * sE = &1 /\\ &0 < aE /\\
          c1092mpap_actual %s cE sE uE vE aE /\\ C1092TF_southeast cE sE uE vE aE /\\
          uE + aE <= cE - (&13 / &50) * sE"
    C1092AE_P C1092MPAP_HYPS C1092AE_P C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`])
    C1092MPAP_NORTHEAST_CORE) THEN ASM_REWRITE_TAC[c1092mtfen_core] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpus_pos] o check (fun th ->
    is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mpus_pos`)) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MARN_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cC:real` (X_CHOOSE_THEN `sC:real` (X_CHOOSE_THEN `uC:real`
    (X_CHOOSE_THEN `vC:real` (X_CHOOSE_THEN `aC:real` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `vC:real`; `--uC - aC`; `aC:real`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092MPAP_INVERSE_ACTUAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `c1092marn_pos c1 c2 a b l cC sC uC vC aC`) THEN
  REWRITE_TAC[c1092marn_pos] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  let hyps4 = end_itlist CONJ [ASSUME C1092MOC_NP; ASSUME C1092MOC_IMG; ASSUME C1092MOC_CTX;
                               ASSUME C1092MOC_OMIT; ASSUME C1092MARN_NEAR_TM] in
  let use4 th = CONV_RULE C1092MOC_CODE_CONV (MP (SPECL C1092MPPE_V th) hyps4) in
  let near = c1092marn_near () in
  let inward = use4 C1092MARN_INWARD_PAIR in
  let bar = use4 C1092MPAP_BAR in
  let mark = c1092moc_seed 7 (`&33 / &20`, `&47 / &20`) in
  let bc = c1092moc_use C1092MOC_BOTTOM_CENTER in
  let sharp6 =
    let eqN = CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term ("!x y. linside cN sN uN vN aN x y <=> " ^
                                 c1092mppe_in 6 "&2 + y" "&2 + x"))) in
    CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (EQ_MP (SPECL [`&47 / &100`; `&3 / &25`] eqN)
             (ASSUME `linside cN sN uN vN aN (&47 / &100) (&3 / &25)`)) in
  let eqC0 = ASSUME (parse_term ("!x y. linside cC sC uC vC l x y <=> " ^
                                 c1092mppe_in 7 "&2 - x" "&2 + y")) in
  let eqE0 = MP (prove(mk_imp(concl eqC0, parse_term ("!x y. linside cC sC vC (--uC - l) l x y <=> " ^
                               c1092mppe_in 7 "&2 + y" "&2 + x")),
    DISCH_TAC THEN ASM_REWRITE_TAC[C1092MTFES_INVERSE_INSIDE; REAL_ARITH `&2 - --x = &2 + x`])) eqC0 in
  let eqE = CONV_RULE C1092MOC_CODE_CONV eqE0 and eqC = CONV_RULE C1092MOC_CODE_CONV eqC0 in
  let pt = c1092mtfes_pt eqE and npt = c1092mtfes_npt eqE in
  let tE = [`cC:real`; `sC:real`; `vC:real`; `--uC - l`; `l:real`] in
  let tB, eqB = c1092mpap_swtr 8 in
  let markE = pt `&7 / &20` `--(&7 / &20)` mark
  and innerE = pt `&0` `--(&13 / &50)` (CONJUNCT2 inward)
  and forwardE = pt `&13 / &50` `&0` (CONJUNCT1 inward)
  and originE = npt `&0` `&0` (c1092moc_excl 7 5 bc)
  and nearE = npt `&1` `--(&13 / &50)` (c1092moc_excl 7 11 near)
  and sharpE = npt `&47 / &100` `&3 / &25` (c1092moc_excl 7 6 sharp6) in
  let barB =
    let x = `x:real` in
    let e = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV))
      (SPECL [x; `--(&1)`] eqB) in
    let pre = CONV_RULE C1092MOC_CODE_CONV (UNDISCH (SPEC x bar)) in
    let pre' = EQ_MP (SYM e) pre in
    GEN x (DISCH `&0 <= x` (DISCH `x <= &2 / &5`
      (PROVE_HYP (CONJ (ASSUME `&0 <= x`) (ASSUME `x <= &2 / &5`)) pre'))) in
  let apartEB =
    let x = `x:real` and y = `y:real` in
    let a1 = SPECL [`&2 + y`; `&2 + x`] (c1092moc_apart 7 8) in
    let eqB' = CONV_RULE C1092MOC_CODE_CONV eqB in
    let a2 = REWRITE_RULE[GSYM (SPECL [x; y] eqE); GSYM (SPECL [x; y] eqB')] a1 in
    let ld = REWRITE_CONV[ldisj] (list_mk_comb(`ldisj`, tE @ tB)) in
    EQ_MP (SYM ld) (GENL [x; y] a2) in
  let gen_facts = [ASSUME `cC * cC + sC * sC = &1`; c1092moc_pos (); c1092moc_side ();
                   markE; innerE; forwardE; originE; nearE; sharpE; barB; apartEB] in
  MAP_EVERY ASSUME_TAC gen_facts THEN
  MP_TAC(SPECL tE C1092MTFF_SOUTHEAST_CAPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; STRIP_TAC] THEN
  ASM_REWRITE_TAC[C1092TF_southeast] THEN
  SUBGOAL_THEN `&1 < l /\ &0 < cC` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 7 "&8 / &5" "&3")) THENL
   [(let outer = CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mppe_in 7 "&8 / &5" "&3"))) in
    let outerE = pt `&1` `--(&2 / &5)` outer in
    ASSUME_TAC outerE THEN
    MP_TAC(SPECL tE C1092MTFF_SOUTHEAST_OUTER_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL (tE @ tB) C1092MTFF_SOUTHEAST_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL tE C1092MTFF_SOUTHEAST_OUTER_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);
    (let missing = CONV_RULE C1092MOC_CODE_CONV
       (ASSUME (mk_neg (parse_term (c1092mppe_in 7 "&8 / &5" "&3")))) in
     let bar7 =
       let y = `y:real` in
       GEN y (DISCH `&0 <= y /\ y <= &2 / &5`
         (c1092moc_excl 7 8 (CONV_RULE C1092MOC_CODE_CONV
            (MP (SPEC y bar) (ASSUME `&0 <= y /\ y <= &2 / &5`))))) in
     let small = c1092moc_apply (c1092moc_conv [eqC])
       (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`] C1092MPIH_SMALL_ANGLE_OF_BAR)
       [ASSUME `cC * cC + sC * sC = &1`; c1092moc_pos (); c1092moc_side ();
        ASSUME `c977cc_normal cC sC`; mark; CONJUNCT1 inward; CONJUNCT2 inward;
        c1092moc_excl 7 5 bc; missing; bar7] in
     STRIP_ASSUME_TAC (CONJUNCT2 small) THEN
     MP_TAC(SPECL (tE @ tB) C1092MTFF_SOUTHEAST_FLOOR) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `sC < &21 / &100` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     MAP_EVERY UNDISCH_TAC [`sC < &21 / &100`; `&97 / &100 < cC`] THEN REAL_ARITH_TAC)]);;

(* (hb 3).1: the right wall owner's center is right of x = 2 *)
let C1092MPAP_RIGHT_CUT = prove
 (parse_term (Printf.sprintf "!%s. %s ==> &2 <= lcx %s" C1092AE_P C1092MPPE_CTX
    (String.concat " " (map (fun f -> Printf.sprintf "(%s c1 c2 a b l (EL 11 c1092wc_code))" f)
       ["ooc"; "oos"; "oou"; "oov"]) ^ " l")),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN DISCH_THEN(MP_TAC o SPEC `3`) THEN
  REWRITE_TAC[c1092mppe_mppm; ARITH] THEN
  REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: right_profile *)
let C1092MPAP_RIGHT_PROFILE =
  let tR, eqR = c1092mpap_swtr 11 in
  prove
   (list_mk_forall(C1092MPPE_V, mk_imp(parse_term C1092MPAP_HYPS, list_mk_comb(`C1092TF_right`, tR))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL C1092MPPE_V C1092MPAP_RIGHT_CUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL C1092MPPE_V C1092MPRI_OTHER_ORDINARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL (C1092MPPE_V @ [`EL 11 c1092wc_code`]) OO_BOX) THEN
    MP_TAC(SPECL (C1092MPPE_V @ [`EL 11 c1092wc_code`]) OO_UNIT) THEN
    ASM_REWRITE_TAC[lcont] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[C1092TF_right; eqR] THEN CONV_TAC C1092MOC_CODE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`&87 / &50`; `&12 / &5`] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
      RASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
      DISCH_THEN(MP_TAC o SPECL [`&2 + y`; `&2 + x`]) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (let q = c1092moc_own 11 in
       let lcyR = list_mk_comb(`lcy`, tR) and lcxq = list_mk_comb(`lcx`, q) in
       SUBGOAL_THEN (mk_eq(lcyR, mk_binop `(-):real->real->real` lcxq `&2`)) SUBST1_TAC THENL
        [MP_TAC (c1092moc_unit 11) THEN REWRITE_TAC[lcx; lcy] THEN CONV_TAC REAL_RING;
         RASM_ARITH_TAC])]);;
