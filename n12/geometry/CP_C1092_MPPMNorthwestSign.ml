(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNorthwestSign.lean                   *)
(* (N12Compact.C1092MPPMNorthwestSign).  The actual mixed-left square        *)
(* excludes the nonpositive northwest angle.  Squares W, N, L are the        *)
(* 5-tuples (cW,..,aW), (cN,..,aN), (cL,..,aL) with explicit OpenSquare      *)
(* invariants; apart is ldisj; Normal is c977cc_normal (normal_bounds        *)
(* C977CC_NORMAL_BOUNDS); MPPMUpperSign.Faces is c1092mpus_faces.            *)
(* lower / upper: ABT_lower / ABT_upper; strict_bounds ABT_STRICT_BOUNDS;    *)
(* ownU ABT_OWNU; faceSeparation_of_disjoint + separated + parallel /        *)
(* transverse_radius: ABT_FOUR_AXES; C1092MixedCornerSupports.               *)
(* negative_support C1092MCSUP_NEGATIVE_SUPPORT; formulas / lower_nn         *)
(* C1092WS_FORMULAS / C1092WS_LOWER_NN; clockwise (c,s,u,v,a) =              *)
(* (c,s,--v-a,u,a), inside_clockwise C1092MEA_INSIDE_CLOCKWISE;              *)
(* MMMMFirstPair.positive_support C1092MFP_POSITIVE_SUPPORT;                 *)
(* MMMMPairScalars.small_of_support C1092MPS_SMALL_OF_SUPPORT;               *)
(* MPPMNorthwestSignScalars C1092MNWS_*.  Tag C1092MPNW_.                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNorthwestSignScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMUpperSign.ml";;
needs "n12/geometry/CP_C1092_MMMMFirstPair.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;

let C1092MPNW_LIN = NLIN_TAC ~deg2:false [];;

(* products of two factors whose signs follow linearly from the assumptions *)
let C1092MPNW_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MPNW_LIN;
     ALL_TAC]) tms;;

(* close a goal by contradiction with a negated linside assumption *)
let C1092MPNW_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg (concl th) then TRUTH else
    REWRITE_RULE[linside] th) THEN
  REWRITE_TAC[linside] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN C1092MPNW_LIN;;

let C1092MPNW_UNITS = prove
 (`forall c s. c * c + s * s = &1
         ==> c pow 2 + s pow 2 = &1 /\ (--c) pow 2 + (--s) pow 2 = &1 /\
             (--s) pow 2 + c pow 2 = &1 /\ s pow 2 + (--c) pow 2 = &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* the separator cone of Lean's axes (local `cone`) *)
let C1092MPNW_CONE = prove
 (`forall cW sW uW vW aW cL sL uL vL aL nx ny.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cL sL uL vL aL (--(&1)) (&2 / &5) /\
     linside cL sL uL vL aL (--(&1)) (&7 / &20) /\
     linside cL sL uL vL aL (--(&1)) (--(&39 / &100)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cL sL uL vL aL nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> &0 < nx /\ &0 < (&13 / &20) * nx + (&37 / &50) * ny /\ &0 < nx - (&2 / &5) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let sb q x y = SPECL (q @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS in
  let qW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
  and qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] in
  MP_TAC(sb qL `--(&1)` `&7 / &20`) THEN MP_TAC(sb qW `--(&7 / &20)` `&7 / &20`) THEN
  MP_TAC(sb qL `--(&1)` `--(&39 / &100)`) THEN MP_TAC(sb qL `--(&1)` `&2 / &5`) THEN
  MP_TAC(sb qW `&0` `&0`) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `ABT_upper cL sL uL vL aL nx ny <= ABT_lower cW sW uW vW aW nx ny` THEN
  REAL_ARITH_TAC);;

(* Lean: axes (private) *)
let C1092MPNW_AXES = prove
 (`forall cW sW uW vW aW cL sL uL vL aL.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     aW = aL /\ c977cc_normal cW (--sW) /\ --sW < &7 / &50 /\ &99 / &100 < cW /\
     c977cc_normal cL sL /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cL sL uL vL aL (--(&1)) (&2 / &5) /\
     linside cL sL uL vL aL (--(&1)) (&7 / &20) /\
     linside cL sL uL vL aL (--(&1)) (--(&39 / &100)) /\
     ldisj cW sW uW vW aW cL sL uL vL aL
     ==> ABT_upper cL sL uL vL aL cW sW <= uW \/
         uL + aL <= ABT_lower cW sW uW vW aW cL sL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aL`)) THEN
  let qW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`]
  and qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] in
  MP_TAC(SPECL [`cW:real`; `sW:real`] C1092MPNW_UNITS) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`] C1092MPNW_UNITS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (qL @ qW) ABT_FOUR_AXES) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ldisj cW sW uW vW aL cL sL uL vL aL` THEN
    REWRITE_TAC[ldisj] THEN MESON_TAC[];
    ALL_TAC] THEN
  let own q = MP (SPECL q ABT_OWNU) (CONJ (ASSUME (list_mk_comb(`(=):real->real->bool`,
      [mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (el 0 q) (el 0 q))
                 (mk_binop `( * ):real->real->real` (el 1 q) (el 1 q)); `&1`])))
      (ASSUME `&0 < aL`)) in
  let owns = [own qW; own qL] in
  STRIP_TAC THEN
  (FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_upper a b c d e (nx:real) (ny:real) <= ABT_lower f g h i j nx ny`) (concl th)
     then MP_TAC th THEN REWRITE_TAC owns THEN SIMP_TAC[] THEN NO_TAC else NO_TAC) ORELSE
  (* every remaining case: a separation of L below W along some n gives a cone
     condition (possibly after reversing a separation of W below L) *)
  FIRST_X_ASSUM(fun th ->
    if not (can (term_match [] `ABT_upper a b c d e (nx:real) (ny:real) <= ABT_lower f g h i j nx ny`)
            (concl th)) then NO_TAC else
    let args = snd (strip_comb (lhand (concl th))) in
    let th' =
      if el 0 args = `cL:real` then th else
      let nx = el 5 args and ny = el 6 args in
      let target = mk_comb(mk_comb(`(<=):real->real->bool`,
            list_mk_comb(`ABT_upper`, qL @ [mk_comb(`(--):real->real`, nx); mk_comb(`(--):real->real`, ny)])),
            list_mk_comb(`ABT_lower`, qW @ [mk_comb(`(--):real->real`, nx); mk_comb(`(--):real->real`, ny)])) in
      let rev = prove(mk_imp(concl th, target),
        REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN REAL_ARITH_TAC) in
      REWRITE_RULE[REAL_NEG_NEG] (MP rev th) in
    let args' = snd (strip_comb (lhand (concl th'))) in
    MP_TAC(SPECL (qW @ qL @ [el 5 args'; el 6 args']) C1092MPNW_CONE) THEN
    ASM_REWRITE_TAC[th'] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092MPNW_LIN)));;

let C1092MPNW_NB_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;
let C1092MPNW_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in
       is_comb t && fst (strip_comb t) = `linside`) ths));;
(* Lean: nonpositive_impossible *)
let C1092MPNW_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cN sN uN vN aN cL sL uL vL aL.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aW /\ aW = aN /\ aW = aL /\
     c977cc_normal cW (--sW) /\ c977cc_normal cN sN /\ &0 < sN /\
     c1092mpus_faces cN sN uN vN aN /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&1 / &2) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cW sW uW vW aW (&7 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&2 / &5) (&1) /\
     c977cc_normal cL sL /\ &5 / &4 < cL + sL /\ lcy cL sL uL vL aL <= &0 /\
     linside cL sL uL vL aL (--(&1)) (&2 / &5) /\
     linside cL sL uL vL aL (--(&1)) (&7 / &20) /\
     linside cL sL uL vL aL (--(&1)) (--(&39 / &100)) /\
     ldisj cW sW uW vW aW cN sN uN vN aN /\
     ldisj cW sW uW vW aW cL sL uL vL aL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aL`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpus_faces] o
    check (can (term_match [] `c1092mpus_faces c s u v a`) o concl)) THEN
  C1092MPNW_NB_TAC THEN
MP_TAC(SPECL [`cW:real`; `sW:real`; `--vW - aW`; `uW:real`; `aW:real`;
                `cN:real`; `sN:real`; `--vN - aW`; `uN:real`; `aW:real`] C1092MFP_POSITIVE_SUPPORT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ldisj; C1092MEA_INSIDE_CLOCKWISE; REAL_NEG_NEG; REAL_NEG_0] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [C1092MPNW_LIN;
           UNDISCH_TAC `ldisj cW sW uW vW aW cN sN uN vN aW` THEN REWRITE_TAC[ldisj] THEN MESON_TAC[]];
    DISCH_TAC] THEN
C1092MPNW_UNFOLD_TAC THEN
  SUBGOAL_THEN `aW <= cN + sN - (cN * cW - sN * --sW) * (uW + aW) - (cN * --sW + sN * cW) * (vW + aW)`
    ASSUME_TAC THENL [C1092MPNW_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --vW /\ &0 < uW + aW /\ &0 < vW + aW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092MPNW_LIN; ALL_TAC] THEN
SUBGOAL_THEN `--vW <= (&7 / &20) * (cW + --sW)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPNW_MISS_TAC `~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20))`; ALL_TAC] THEN
MP_TAC(SPECL [`cW:real`; `--sW`; `cN:real`; `sN:real`; `aW:real`; `--vW`; `uW + aW`]
    C1092MPS_SMALL_OF_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MPNW_LIN; STRIP_TAC] THEN
SUBGOAL_THEN `uW + aW <= &7 / &20 * (cW - --sW)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPNW_MISS_TAC `~linside cW sW uW vW aW (&7 / &20) (&7 / &20)`; ALL_TAC] THEN
SUBGOAL_THEN `&1 - &7 / &20 * (cW + --sW) <= vW + aW` ASSUME_TAC THENL
   [C1092MPNW_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`] C1092MNWS_UPPER_SPAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092MPNW_PROD_TAC [`&0 <= sN * (cW + --sW - &1)`; `&0 <= (cN - sN) * --sW`;
                      `&0 <= (cN - sN) * cW`; `&0 <= sN * (cW - --sW)`;
                      `&0 <= cN * --sW`; `&0 < sN * cW`] THEN
  SUBGOAL_THEN `sN <= cN * --sW + sN * cW /\ &0 <= cN * cW - sN * --sW /\
                &0 < cN * --sW + sN * cW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092MPNW_LIN; ALL_TAC] THEN
SUBGOAL_THEN `vW + aW < &41 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPNW_PROD_TAC [`&0 <= (cN * cW - sN * --sW) * (uW + aW)`;
                        `&0 <= (cN * --sW + sN * cW) * ((vW + aW) - &41 / &50)`] THEN
    C1092MPNW_LIN; ALL_TAC] THEN
ABBREV_TAC `PF = cN * (&1 - cW * (uW + aW) - --sW * (vW + aW)) + sN * (&1 - cW * (vW + aW) + --sW * (uW + aW))` THEN
  ABBREV_TAC `QF = sN * (&1 - cW * (uW + aW) - --sW * (vW + aW)) - cN * (&1 - cW * (vW + aW) + --sW * (uW + aW))` THEN
  SUBGOAL_THEN `&1 < PF` ASSUME_TAC THENL
   [EXPAND_TAC "PF" THEN C1092MPNW_LIN; ALL_TAC] THEN
  C1092MPNW_PROD_TAC [`&0 < (PF - &1) * (PF + &1)`] THEN
  SUBGOAL_THEN `(uW + aW) pow 2 + (vW + aW) pow 2 - &2 * (cW - --sW) * (uW + aW) -
                &2 * (cW + --sW) * (vW + aW) + &1 = PF pow 2 + QF pow 2 - &1` ASSUME_TAC THENL
   [EXPAND_TAC "PF" THEN EXPAND_TAC "QF" THEN
    MAP_EVERY UNDISCH_TAC [`cW * cW + sW * sW = &1`; `cN * cN + sN * sN = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (uW + aW) pow 2 + (vW + aW) pow 2 - &2 * (cW - --sW) * (uW + aW) -
                &2 * (cW + --sW) * (vW + aW) + &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false [SQ_NONNEG `QF:real`]; ALL_TAC] THEN
MP_TAC(SPECL [`cW:real`; `--sW`; `uW + aW`; `vW + aW`] C1092MNWS_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aW:real`] C1092MPNW_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`] C1092MNWS_WALL_SINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092MPNW_PROD_TAC [`&0 < cL * (cW - --sW)`; `&0 <= --sW * (cL - sL)`;
                      `&0 < cW * sL`; `&0 <= --sW * cL`] THEN
  SUBGOAL_THEN `&0 < cW * cL - --sW * sL /\ &0 < cW * sL + --sW * cL /\
                --cL + &2 / &5 * sL < uL + aW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092MPNW_LIN; ALL_TAC] THEN
  STRIP_TAC THENL
  [(* centralAxis *)
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aW:real`; `cW:real`; `sW:real`]
    C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < cW * cL + sW * sL /\ --cW * sL + sW * cL <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MPNW_LIN; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> max d (&0) = d`; REAL_ARITH `d <= &0 ==> max d (&0) = &0`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(cW * cL + sW * sL) * (uL + aW) + (--cW * sL + sW * cL) * vL <= uW` ASSUME_TAC THENL
   [UNDISCH_TAC `ABT_upper cL sL uL vL aW cW sW <= uW` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `lcy cL sL uL vL aW <= &0` THEN REWRITE_TAC[lcy] THEN DISCH_TAC THEN
  C1092MPNW_PROD_TAC [`&0 <= aW * (cL - sL)`] THEN
  SUBGOAL_THEN `sL * (uL + aW) + cL * vL <= &0` ASSUME_TAC THENL [C1092MPNW_LIN; ALL_TAC] THEN
  C1092MPNW_PROD_TAC [`&0 <= (cW * sL + --sW * cL) * --(sL * (uL + aW) + cL * vL)`;
                      `&0 < cW * ((uL + aW) - (--cL + &2 / &5 * sL))`;
                      `&0 <= cL * (uW - ((cW * cL + sW * sL) * (uL + aW) + (--cW * sL + sW * cL) * vL))`;
                      `&0 < cL * (aW - cW)`; `&0 <= (uW + aW) * (&1 - cL)`;
                      `&0 < (cW - &99 / &100) * sL`] THEN
  SUBGOAL_THEN `cL * ((cW * cL + sW * sL) * (uL + aW) + (--cW * sL + sW * cL) * vL) =
                cW * (uL + aW) - (cW * sL + --sW * cL) * (sL * (uL + aW) + cL * vL)` ASSUME_TAC THENL
   [UNDISCH_TAC `cL * cL + sL * sL = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MPNW_LIN;
  (* leftAxis *)
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `cL:real`; `sL:real`;
                `cL * cW + sL * sW`; `--cL * sW + sL * cW`] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN C1092MPNW_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--sW`; `cL:real`; `sL:real`] C1092MNWS_WALL_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092MPNW_PROD_TAC [`&0 < (cW * cL - --sW * sL) * (--(&9 / &10) - uW)`;
                      `&0 < (cW * sL + --sW * cL) * (--(&9 / &50) - vW)`] THEN
  UNDISCH_TAC `uL + aW <= ABT_lower cW sW uW vW aW cL sL` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN C1092MPNW_LIN]);;
