(* ========================================================================= *)
(* Port of Compact/Geometry/C977ChainBridge.lean (N12Compact.C977ChainBridge)*)
(* Adapter from OpenSquare support data to the generic wall-chain cut.      *)
(*                                                                           *)
(* Squares are 5-tuples c s u v a (see p2_base.ml); centerX/Y = lcx/lcy.     *)
(* normalDot q r = cq * cr + sq * sr, normalCross q r = cq * sr - sq * cr    *)
(* (inlined, as in C977WallChains.ml).                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallChain.ml";;
needs "n12/geometry/C977WallChains.ml";;

(* Lean: pairRadius *)
let C977CB_pairRadius = new_definition
 `C977CB_pairRadius (cq:real) (sq:real) (aq:real) (cr:real) (sr:real) (ar:real) =
    aq / &2 + ar / &2 * (abs(cq * cr + sq * sr) + abs(cq * sr - sq * cr))`;;

(* Lean: FaceSeparation *)
let C977CB_faceSep = new_definition
 `C977CB_faceSep cq sq uq vq aq cr sr ur vr ar <=>
    C977CB_pairRadius cq sq aq cr sr ar <=
      abs(cq * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
          sq * (lcy cr sr ur vr ar - lcy cq sq uq vq aq)) \/
    C977CB_pairRadius cq sq aq cr sr ar <=
      abs(--sq * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
          cq * (lcy cr sr ur vr ar - lcy cq sq uq vq aq)) \/
    C977CB_pairRadius cr sr ar cq sq aq <=
      abs(cr * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
          sr * (lcy cr sr ur vr ar - lcy cq sq uq vq aq)) \/
    C977CB_pairRadius cr sr ar cq sq aq <=
      abs(--sr * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
          cr * (lcy cr sr ur vr ar - lcy cq sq uq vq aq))`;;

(* Lean: near_axis_projection_bounds *)
let C977CB_NEAR_AXIS_PROJECTION_BOUNDS = prove
 (`forall c s X Y h.
     c * c + s * s = &1 /\ (&0 <= c /\ abs s <= &1 / &10) /\
     &0 <= X /\ abs Y <= h /\
     &0 < (&99 / &100) * X - (&1 / &10) * h /\
     (&1 / &10) * X + h < &1
     ==> &0 < c * X + s * Y /\ abs(--s * X + c * Y) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977WC_NEAR_AXIS_COS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  REWRITE_TAC[REAL_ARITH `abs x < d <=> --d < x /\ x < d`] THEN
  NLIN_FACTS_TAC [] [`&0 <= h`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

let C977CB_USE th =
  MP_TAC th THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRY RASM_ARITH_TAC; STRIP_TAC];;

(* instantiate every assumption !i. P i ==> Q i at t, when i < n implies P t *)
let C977CB_INST_AT_TAC t (asl,w as g) =
  let hyp = `(i:num) < (n:num)` in
  let one th =
    try let th1 = SPEC t th in
        let ant = lhand(concl th1) in
        [MP th1 (MP (ARITH_RULE (mk_imp(hyp,ant))) (ASSUME hyp))]
    with Failure _ -> [] in
  let ths = flat (map (one o snd) (filter (fun (_,th) -> is_forall(concl th)) asl)) in
  MAP_EVERY (STRIP_ASSUME_TAC o PROVE_HYP (ASSUME hyp)) ths g;;

(* Lean: pair_step_of_face_separation, first in coordinates X Y *)
let C977CB_PAIR_STEP_XY = prove
 (`forall cq sq cr sr a h X Y.
     cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1 /\ &1 < a /\
     (&0 <= cq /\ abs sq <= &1 / &10) /\ (&0 <= cr /\ abs sr <= &1 / &10) /\
     &0 <= X /\ abs Y <= h /\
     &0 < (&99 / &100) * X - (&1 / &10) * h /\
     (&1 / &10) * X + h < &1 /\
     (C977CB_pairRadius cq sq a cr sr a <= abs(cq * X + sq * Y) \/
      C977CB_pairRadius cq sq a cr sr a <= abs(--sq * X + cq * Y) \/
      C977CB_pairRadius cr sr a cq sq a <= abs(cr * X + sr * Y) \/
      C977CB_pairRadius cr sr a cq sq a <= abs(--sr * X + cr * Y))
     ==> exists b. (b = sq \/ b = sr) /\
             a + a * (&43 / &100) * abs(sr - sq) - b * Y <= X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C977CB_USE(SPECL [`cq:real`; `sq:real`] C977WC_NEAR_AXIS_COS) THEN
  C977CB_USE(SPECL [`cr:real`; `sr:real`] C977WC_NEAR_AXIS_COS) THEN
  C977CB_USE(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`]
    C977WC_NEAR_AXIS_RELATIVE_BOUNDS) THEN
  C977CB_USE(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`]
    C977WC_NEAR_AXIS_PAIR_GAIN) THEN
  C977CB_USE(SPECL [`cq:real`; `sq:real`; `X:real`; `Y:real`; `h:real`]
    C977CB_NEAR_AXIS_PROJECTION_BOUNDS) THEN
  C977CB_USE(SPECL [`cr:real`; `sr:real`; `X:real`; `Y:real`; `h:real`]
    C977CB_NEAR_AXIS_PROJECTION_BOUNDS) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
  SUBGOAL_THEN
   `C977CB_pairRadius cq sq a cr sr a =
      a / &2 * (&1 + (cq * cr + sq * sr) + abs(cq * sr - sq * cr)) /\
    C977CB_pairRadius cr sr a cq sq a =
      a / &2 * (&1 + (cq * cr + sq * sr) + abs(cq * sr - sq * cr))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[C977CB_pairRadius] THEN
    SUBGOAL_THEN `abs(cq * cr + sq * sr) = cq * cr + sq * sr /\
                  abs(cr * cq + sr * sq) = cq * cr + sq * sr /\
                  abs(cr * sq - sr * cq) = abs(cq * sr - sq * cr)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = cq * cr + sq * sr` THEN
  ABBREV_TAC `C = abs(cq * sr - sq * cr)` THEN
  ABBREV_TAC `G = abs(sr - sq)` THEN
  SUBGOAL_THEN `&0 <= G /\ &0 <= C` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "C"] THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`a + a * (&43 / &100) * G <= a / &2 * (&1 + D + C)`;
    `&1 < a / &2 * (&1 + D + C)`;
    `cq * X <= X`; `cr * X <= X`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [EXISTS_TAC `sq:real` THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN RASM_ARITH_TAC;
    EXISTS_TAC `sr:real` THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN RASM_ARITH_TAC]);;

(* Lean: pair_step_of_face_separation *)
let C977CB_PAIR_STEP_OF_FACE_SEPARATION = prove
 (`forall cq sq uq vq aq cr sr ur vr ar a h.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     &1 < a /\ aq = a /\ ar = a /\
     (&0 <= cq /\ abs sq <= &1 / &10) /\ (&0 <= cr /\ abs sr <= &1 / &10) /\
     &0 <= lcx cr sr ur vr ar - lcx cq sq uq vq aq /\
     abs(lcy cr sr ur vr ar - lcy cq sq uq vq aq) <= h /\
     &0 < (&99 / &100) * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) - (&1 / &10) * h /\
     (&1 / &10) * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) + h < &1 /\
     C977CB_faceSep cq sq uq vq aq cr sr ur vr ar
     ==> exists b. (b = sq \/ b = sr) /\
             a + a * (&43 / &100) * abs(sr - sq) -
               b * (lcy cr sr ur vr ar - lcy cq sq uq vq aq) <=
             lcx cr sr ur vr ar - lcx cq sq uq vq aq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let l,r = dest_eq(concl th) in is_var l && r = `a:real`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C977CB_faceSep]) THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`; `a:real`; `h:real`;
    `lcx cr sr ur vr a - lcx cq sq uq vq a`; `lcy cr sr ur vr a - lcy cq sq uq vq a`]
    C977CB_PAIR_STEP_XY) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: openSquare_chain_cut *)
let C977CB_OPENSQUARE_CHAIN_CUT = prove
 (`forall n (c:num->real) (s:num->real) (u:num->real) (v:num->real) (sd:num->real)
    a lower h.
     (forall i. i <= n ==> c i * c i + s i * s i = &1 /\ &0 < sd i) /\
     &1 < a /\ h <= &43 / &100 /\
     (forall i. i <= n ==> sd i = a) /\
     (forall i. i <= n ==> &0 <= c i /\ abs(s i) <= &1 / &10) /\
     (forall i. i <= n ==> lower <= lcy (c i) (s i) (u i) (v i) (sd i) /\
                     lcy (c i) (s i) (u i) (v i) (sd i) <= lower + h) /\
     (forall i. i < n ==>
        &0 <= lcx (c(i + 1)) (s(i + 1)) (u(i + 1)) (v(i + 1)) (sd(i + 1)) -
              lcx (c i) (s i) (u i) (v i) (sd i) /\
        &0 < (&99 / &100) *
              (lcx (c(i + 1)) (s(i + 1)) (u(i + 1)) (v(i + 1)) (sd(i + 1)) -
               lcx (c i) (s i) (u i) (v i) (sd i)) - (&1 / &10) * h /\
        (&1 / &10) *
              (lcx (c(i + 1)) (s(i + 1)) (u(i + 1)) (v(i + 1)) (sd(i + 1)) -
               lcx (c i) (s i) (u i) (v i) (sd i)) + h < &1) /\
     (forall i. i < n ==> C977CB_faceSep (c i) (s i) (u i) (v i) (sd i)
                      (c(i + 1)) (s(i + 1)) (u(i + 1)) (v(i + 1)) (sd(i + 1))) /\
     (forall x y. linside (c n) (s n) (u n) (v n) (sd n) x y
            ==> &0 <= x /\ x <= &4 /\ &0 <= y /\ y <= &4)
     ==> lcx (c 0) (s 0) (u 0) (v 0) (sd 0) < &4 - (&n + &1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `forall i. exists bi. i < n ==>
      (bi = s i \/ bi = s(i + 1)) /\
      a + a * (&43 / &100) * abs(s(i + 1) - s i) -
        bi * (lcy (c(i + 1)) (s(i + 1)) (u(i + 1)) (v(i + 1)) (sd(i + 1)) -
              lcy (c i) (s i) (u i) (v i) (sd i)) <=
      lcx (c(i + 1)) (s(i + 1)) (u(i + 1)) (v(i + 1)) (sd(i + 1)) -
      lcx (c i) (s i) (u i) (v i) (sd i)`
  MP_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `(i:num) < n` THEN ASM_REWRITE_TAC[] THEN
    C977CB_INST_AT_TAC `i:num` THEN C977CB_INST_AT_TAC `i + 1` THEN
    MATCH_MP_TAC C977CB_PAIR_STEP_OF_FACE_SEPARATION THEN
    EXISTS_TAC `h:real` THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC WCH_HEIGHT_DISTANCE THEN EXISTS_TAC `lower:real` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `b:num->real`)] THEN
  MP_TAC(SPECL [`(c:num->real) n`; `(s:num->real) n`; `(u:num->real) n`; `(v:num->real) n`;
                `(sd:num->real) n`]
    C977WC_NEAR_AXIS_RIGHT_WALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; DISCH_TAC] THEN
  SUBGOAL_THEN `(sd:num->real) n = a` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(SPECL
   [`n:num`; `\i. lcx ((c:num->real) i) ((s:num->real) i) ((u:num->real) i)
                       ((v:num->real) i) ((sd:num->real) i)`;
    `\i. lcy ((c:num->real) i) ((s:num->real) i) ((u:num->real) i)
                       ((v:num->real) i) ((sd:num->real) i)`; `s:num->real`; `b:num->real`;
    `a:real`; `&43 / &100`; `lower:real`; `h:real`; `&4`] WCH_FIRST_CENTER_CUT)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `&43 / &100`)) (concl th)
                 && can (find_term ((=) `lcx`)) (concl th)
                 && not (is_forall (concl th)) && not (is_imp (concl th)))) THEN
    ASM_REWRITE_TAC[]]);;
