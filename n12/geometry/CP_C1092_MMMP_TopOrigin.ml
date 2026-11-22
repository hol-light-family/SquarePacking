(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TopOrigin.lean                      *)
(* (N12Compact.C1092MMMPTopOrigin).  The genuine left-wall/corner           *)
(* interaction supplies the top wall's origin in the MMMP branch.           *)
(* Conventions of CP_C1092_MMMP_Origins.ml / CP_C1092_MMMP_TopOriginSign.ml *)
(* (owners p i at mask EL i c1092wc_code, side l; charts via c1092mo_layers;*)
(* owners p 3 / 8 / 11 = owner 192 / 4096 / 32768).  Lean `upper` is        *)
(* ABT_upper; WallProfile.positive_frame / upper_turnFrame =                *)
(* OCWPSG_POSITIVE_FRAME / OCWPSG_UPPER_TURNFRAME; boundary_origin_of_profile*)
(* = OCWPBO_BOUNDARY_ORIGIN_OF_PROFILE; NegativeCornerFloor.                *)
(* nonnegative_impossible / floor = C1092MMNCF_*; CornerFloorProfile.       *)
(* support_profile = C1092MCFP_SUPPORT_PROFILE; profile = C1092WPS_profile;  *)
(* Normal = c977cc_normal; negative_left_of_missing_top / corner_halfpoint / *)
(* top_alternative = C1092MTOS_*; LeftFar.point = C1092MLF_POINT;           *)
(* p.side_le = OO_SIDE_LE.  pullY q = (c, --s, u - 4 s, 4 c - v - a, a)       *)
(* (LINSIDE_PULLY), q.translated 1 2 that of CCIP_INSIDE_TRANSLATED.         *)
(* Tag C1092MMTO_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_TopOriginSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_NegativeCornerFloor.ml";;
needs "n12/geometry/CP_C1092_MMMP_CornerFloorProfile.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;

(* the third iterate of turnFrame keeps the support function *)
let C1092MMTO_UPPER_TURN3 = prove
 (`forall c s u v a nx ny. ABT_upper s (--c) (--v - a) u a nx ny = ABT_upper c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `nx * s + ny * --c = --(--nx * s + ny * c)`;
              REAL_ARITH `--nx * --c + ny * s = nx * c + ny * s`; REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

(* Lean: canonical_support_frame (private) *)
let C1092MMTO_CANONICAL_SUPPORT_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ abs s' <= c' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           (forall nx ny. ABT_upper c' s' u' v' a' nx ny = ABT_upper c s u v a nx ny)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCWPSG_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `s1 <= c1` THENL
   [MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`s1:real`; `--c1:real`; `--v1 - a1:real`; `u1:real`; `a1:real`] THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) then REWRITE_TAC[GSYM th] else NO_TAC)) THEN
    REWRITE_TAC[C1092MMTO_UPPER_TURN3; REAL_NEG_MUL2; REAL_ABS_NEG] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `c1 * c1 + s1 * s1 = &1` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      REWRITE_TAC[linside] THEN REPEAT GEN_TAC THEN REAL_ARITH_TAC]]);;

(* closes hypotheses about a reframed square R through the iff th : R <-> K *)
let C1092MMTO_CLOSE_TAC th =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[th; ldisj] THEN
         FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM MATCH_ACCEPT_TAC;
                FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[ldisj])];
         RASM_ARITH_TAC];;

(* Lean: corner_profile (private) *)
let C1092MMTO_CORNER_PROFILE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK nx ny.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL <= &2 /\ aL = aK /\ c977cc_normal cL (--sL) /\ sL < &0 /\
     lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&1) <= x) /\
     (forall x y. linside cK sK uK vK aK x y ==> --(&1) <= x) /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK /\
     &0 <= nx /\ &0 <= ny /\ nx pow 2 + ny pow 2 = &1
     ==> aK * C1092WPS_profile nx ny - nx + &2 * ny <= ABT_upper cK sK uK vK aK nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`]
    C1092MMTO_CANONICAL_SUPPORT_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `ABT_upper`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR:real = aK`)) THEN
  FIRST_X_ASSUM(fun iff -> if is_forall(concl iff) && is_iff(snd(strip_forall(concl iff)))
    then
      SUBGOAL_THEN `sR < &0` ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
        SUBGOAL_THEN `c977cc_normal cR sR` ASSUME_TAC THENL
         [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN C1092MMTO_CLOSE_TAC iff; ALL_TAC] THEN
        MATCH_MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                            `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aK:real`]
                           C1092MMNCF_NONNEGATIVE_IMPOSSIBLE) THEN
        C1092MMTO_CLOSE_TAC iff;
        ALL_TAC] THEN
      SUBGOAL_THEN `c977cc_normal cR (--sR)` ASSUME_TAC THENL
       [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN C1092MMTO_CLOSE_TAC iff;
        ALL_TAC] THEN
      MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aK:real`] C1092MMNCF_FLOOR) THEN
      ANTS_TAC THENL [C1092MMTO_CLOSE_TAC iff; DISCH_TAC] THEN
      MATCH_MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aK:real`; `nx:real`; `ny:real`]
                         C1092MCFP_SUPPORT_PROFILE) THEN
      C1092MMTO_CLOSE_TAC iff
    else NO_TAC));;

(* Lean: chart_support (private) *)
let C1092MMTO_CHART_SUPPORT = prove
 (`forall c s u v a nx ny. c * c + s * s = &1
     ==> ABT_upper c (--s) (u - &4 * s) (&4 * c - v - a) a nx (--ny) =
         nx - &2 * ny + ABT_upper c s (u - (c * &1 + s * &2)) (v - (--s * &1 + c * &2)) a nx ny`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
  REWRITE_TAC[REAL_ARITH `nx * c + --ny * --s = nx * c + ny * s`;
              REAL_ARITH `--nx * --s + --ny * c = --(--nx * s + ny * c)`; REAL_ABS_NEG] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

let C1092MMTO_MISSING = "~" ^ c1092mmpe_in 11 "&2" "&3";;

(* Lean: point *)
let C1092MMTO_POINT = prove
 (c1092mmpe_stmt 11 "&2" "&3",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MTOS_NEGATIVE_LEFT_OF_MISSING_TOP) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL C1092MTOS_CORNER_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MTOS_TOP_ALTERNATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> false) ==> ~p`) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM; c1092mtos_negleft] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let tL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] in
  let tLl = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `l:real`] in
  let tQ, eqQ = c1092mo_layers 3 [c1092mo_tr `&1` `&2`] in
  let tB, eqB = c1092mo_layers 11 [C1092MO_Y] in
  let tK, eqK = c1092mo_layers 3 [C1092MO_Y] in
  let far = c1092mo_use C1092MLF_POINT in
  let corner = c1092mo_seed 3 (`&1`, `&3`) in
  let half = ASSUME (c1092mo_in 3 `&1` `&5 / &2`) in
  let alt = ASSUME (c1092mo_in 11 `&6 / &5` `&3`) in
  let box3 = REWRITE_RULE[lcont] (c1092mo_box 3) and box8 = REWRITE_RULE[lcont] (c1092mo_box 8) in
  let cap = MATCH_MP (REAL_ARITH `l <= &1001 / &1000 ==> l <= &2`)
              (MP (SPECL C1092MMPE_V OO_SIDE_LE) (ASSUME C1092MO_NP)) in
  let nxv = `nx:real` and nyv = `ny:real` in
  let full_tm = list_mk_forall([nxv; nyv], mk_imp(
      `&0 <= nx /\ &0 <= ny /\ nx pow 2 + ny pow 2 = &1`,
      mk_binop `(<=):real->real->bool`
        `l * C1092WPS_profile nx ny - nx + &2 * ny`
        (list_mk_comb(`ABT_upper`, tQ @ [nxv; nyv])))) in
  MAP_EVERY X_GEN_TAC tL THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = l`)) THEN
  SUBGOAL_THEN full_tm ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (tLl @ tQ @ [nxv; nyv]) C1092MMTO_CORNER_PROFILE) THEN
    REWRITE_TAC[ldisj] THEN CONV_TAC (c1092mo_conv eqQ) THEN
    FIRST_X_ASSUM(fun iff -> if is_forall(concl iff) && is_iff(snd(strip_forall(concl iff)))
      then REWRITE_TAC[iff] else NO_TAC) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MAP_EVERY ASSUME_TAC [c1092mo_punit 3 tQ; c1092mo_pos (); c1092mo_side (); cap; far; corner;
                          half; c1092mo_excl 3 11 alt] THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
           REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (c1092mo_apart 8 3);
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box3) THEN REAL_ARITH_TAC;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box8) THEN REAL_ARITH_TAC;
           RASM_ARITH_TAC];
    ALL_TAC] THEN
  let profile_tm = list_mk_forall([`c:real`; `s:real`],
        mk_imp(`&0 <= c`, mk_imp(`&0 <= s`, mk_imp(`c pow 2 + s pow 2 = &1`,
          mk_binop `(<=):real->real->bool` `l * C1092WPS_profile c s`
            (list_mk_comb(`ABT_upper`, tK @ [`c:real`; `--s`])))))) in
  SUBGOAL_THEN profile_tm ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL (c1092mo_own 3 @ [`c:real`; `s:real`]) C1092MMTO_CHART_SUPPORT) THEN
    ANTS_TAC THENL [ACCEPT_TAC (c1092mo_unit 3); DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `s:real`] o check (fun th -> concl th = full_tm)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (let profileK = ASSUME profile_tm in
   let disj =
     let tm = list_mk_comb(`ldisj`, tK @ tB) in
     let eq = (REWRITE_CONV[ldisj] THENC c1092mo_conv eqK THENC c1092mo_conv eqB) tm in
     EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL [`x:real`; `&4 - y`] (c1092mo_apart 3 11)))) in
   let top = c1092mo_use C1092MMPE_TOP_PAIR in
   let facts = [c1092mo_punit 11 tB; c1092mo_punit 3 tK; c1092mo_pos (); c1092mo_side ();
                REFL `l:real`; MATCH_MP C1092MO_BOX_Y (c1092mo_plcont 11 [C1092MO_Y]);
                c1092mo_seed 11 (`&2`, `&1543 / &500`); CONJUNCT1 top;
                c1092mo_seed 3 (`&1`, `&1543 / &500`); corner; profileK; disj] in
   let th = c1092mo_apply (c1092mo_conv (eqB @ eqK))
              (SPECL (tB @ tK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN_OF_PROFILE) facts in
   FIRST_X_ASSUM(fun m -> if is_neg (concl m) && rand (concl m) = concl th
     then ACCEPT_TAC (MP (NOT_ELIM m) th) else NO_TAC)));;
