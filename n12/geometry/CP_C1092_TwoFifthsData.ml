(* ========================================================================= *)
(* Port of Compact/Completion/C1092/TwoFifthsData.lean                       *)
(* (N12Compact.C1092TwoFifths).  Literal local input of the two-fifths slope *)
(* squeeze: the Southeast, Northeast, Right and Input structures.            *)
(* exists_positive_frame (S12.SquareSupportBase) is LSEC_POSITIVE_FRAME_RADIUS.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/LongSection.ml";;

(* Lean: Southeast (structure) *)
let C1092TF_southeast = new_definition
 `C1092TF_southeast (c:real) s u v a <=>
    &1 < a /\ &0 < c /\ &0 < s /\ &3 * s < c /\
    linside c s u v a (&0) (--(&13 / &50)) /\
    linside c s u v a (&13 / &50) (&0) /\
    v + a <= &0 /\
    a * (c + s) - &1 < s * (u + a) + c * (v + a)`;;

(* Lean: Northeast (structure) *)
let C1092TF_northeast = new_definition
 `C1092TF_northeast (c:real) s u v a <=>
    &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
    &1 + c < &4 * s /\ &3 * s <= &1 + c /\
    (&2 / &5) * s <= u /\ (&2 / &5) * c - s <= v /\
    u + a <= c + s /\ v + a <= c /\
    linside c s u v a (&7 / &20) (&7 / &20) /\
    linside c s u v a (&2 / &5) (&1) /\
    linside c s u v a (&47 / &100) (&3 / &25)`;;

(* Lean: Right (structure) *)
let C1092TF_right = new_definition
 `C1092TF_right (c:real) s u v a <=>
    (forall y. --(&13 / &50) <= y /\ y <= &2 / &5 ==> linside c s u v a (&1) y) /\
    (forall x y. linside c s u v a x y ==> x <= &2) /\
    &0 <= lcy c s u v a`;;

(* Lean: Input (structure) *)
let C1092TF_input = new_definition
 `C1092TF_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR <=>
    C1092TF_southeast cE sE uE vE aE /\
    C1092TF_northeast cN sN uN vN aN /\
    C1092TF_right cR sR uR vR aR /\
    aE = aR /\ aN = aR /\
    ldisj cE sE uE vE aE cR sR uR vR aR /\
    ldisj cN sN uN vN aN cR sR uR vR aR`;;

(* Lean: Right.reframe *)
let C1092TF_RIGHT_REFRAME = prove
 (`forall cR sR uR vR aR cQ sQ uQ vQ aQ.
     C1092TF_right cR sR uR vR aR /\
     (forall x y. linside cQ sQ uQ vQ aQ x y <=> linside cR sR uR vR aR x y) /\
     lcy cQ sQ uQ vQ aQ = lcy cR sR uR vR aR
     ==> C1092TF_right cQ sQ uQ vQ aQ`,
  REWRITE_TAC[C1092TF_right] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* Lean: canonical_right *)
let C1092TF_CANONICAL_RIGHT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ abs s' <= c' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           lcy c' s' u' v' a' = lcy c s u v a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    LSEC_POSITIVE_FRAME_RADIUS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`; `u0:real`; `v0:real`; `a0:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a0:real = a`)) THEN
  ASM_CASES_TAC `q <= p` THENL
   [MAP_EVERY EXISTS_TAC [`p:real`; `q:real`; `u0:real`; `v0:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `p = &0 /\ q = &0` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `p * p + q * q = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 <= q ==> abs q = q`]];
    MAP_EVERY EXISTS_TAC [`q:real`; `--p`; `--v0 - a`; `u0:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p * p + q * q = &1` THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_NEG] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= p ==> abs p = p`] THEN
      ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) then
        REWRITE_TAC[GSYM th] else failwith "no") THEN
      REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `lcy`)) (concl th)
        then REWRITE_TAC[GSYM th] else failwith "no") THEN
      REWRITE_TAC[lcy] THEN REAL_ARITH_TAC]]);;
