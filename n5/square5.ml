(* ========================================================================= *)
(* s(5) = 2 + sqrt(2)/2: five unit squares in a square.                      *)
(*                                                                           *)
(* Lower bound: Goebel/Friedman "unavoidable points".  If the container has  *)
(* side s = 2 + sqrt(2)/2 - e with 0 < e <= 1/100, then every unit square    *)
(* inside it contains in its interior one of the four points (a,a), (a,b),   *)
(* (b,a), (b,b) with a = 1 - e/4, b = 1 + sqrt(2)/2 - 3e/4.  Five squares    *)
(* with disjoint interiors would need five different points.                 *)
(* Upper bound: Goebel's packing (four corner squares plus one at 45 deg).   *)
(* ========================================================================= *)

needs "shared/squares_lib.ml";;

(* ------------------------------------------------------------------------- *)
(* Elementary real lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

let SQ_LE_IMP = prove
 (`forall x y. &0 <= y /\ x * x <= y * y ==> x <= y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= abs y /\ &0 <= y ==> x <= y`) THEN
  ASM_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC);;

let SQ_LT_IMP = prove
 (`forall x y. &0 <= y /\ x * x < y * y ==> x < y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < abs y /\ &0 <= y ==> x < y`) THEN
  ASM_REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC);;

let R2_BOUNDS = prove
 (`forall r. &0 < r /\ r * r = &2 ==> &1 < r /\ r < &3 / &2`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SQ_LT_IMP; MATCH_MP_TAC SQ_LT_IMP] THEN ASM_REAL_ARITH_TAC);;

let C_LEMMA = prove
 (`forall r e P Q.
        &0 < r /\ r * r = &2 /\ &0 < e /\
        &0 <= P /\ &0 <= Q /\ P * P + Q * Q = &1
        ==> (r / &4 - e / &4) * P + (&1 - e / &4 - (P + Q) / &2) * Q < &1 / &2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP R2_BOUNDS o CONJ (ASSUME `&0 < r`)) THEN
  SUBGOAL_THEN `P <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC SQ_LE_IMP THEN MP_TAC(SPEC `Q:real` REAL_LE_SQUARE) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * (P + Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `P + Q = &0` THENL
     [SUBGOAL_THEN `P = &0 /\ Q = &0` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `P * P + Q * Q = &1` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - Q) * (&1 - Q) / &2 + P * (&2 * Q - r) / &4`
  MP_TAC THENL
   [ASM_CASES_TAC `r <= &2 * Q` THENL
     [MP_TAC(SPEC `&1 - Q` REAL_LE_SQUARE) THEN
      MP_TAC(ISPECL [`P:real`; `&2 * Q - r`] REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`r - &2 * Q`; `P:real`; `&1`] REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `Q - &1 / &2` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let BASIC5 = prove
 (`forall r e P Q.
        &0 < r /\ r * r = &2 /\ &0 < e /\ e <= &1 / &100 /\
        &0 <= P /\ &0 <= Q /\ P * P + Q * Q = &1
        ==> &0 <= r / &4 - e / &4 /\
            &0 <= &1 - e / &4 - (P + Q) / &2 /\
            (r / &4 - e / &4) * (P + Q) < &1 / &2 /\
            (&1 - e / &4 - (P + Q) / &2) * (P + Q) < &1 / &2 /\
            (r / &4 - e / &4) * P + (&1 - e / &4 - (P + Q) / &2) * Q < &1 / &2 /\
            (r / &4 - e / &4) * Q + (&1 - e / &4 - (P + Q) / &2) * P < &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP R2_BOUNDS o CONJ (ASSUME `&0 < r`)) THEN
  SUBGOAL_THEN `P + Q <= r /\ &1 <= P + Q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQ_LE_IMP THEN
    MP_TAC(SPEC `P - Q` REAL_LE_SQUARE) THEN
    MP_TAC(SPECL [`P:real`; `Q:real`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`r / &4 - e / &4`; `P + Q:real`; `r:real`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real`; `r:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`e:real`; `P + Q:real`] REAL_LT_MUL) THEN
    MP_TAC(SPEC `P + Q - &1` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C_LEMMA THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`r:real`; `e:real`; `Q:real`; `P:real`] C_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_SYM]]);;

let CORE_LIN = prove
 (`forall P Q X Y.
        &0 <= P /\ &0 <= Q /\
        (exists lx hx ly hy.
            lx <= X /\ X <= hx /\ ly <= Y /\ Y <= hy /\
            hx * P + hy * Q < &1 / &2 /\ --(lx * P + ly * Q) < &1 / &2 /\
            hx * Q - ly * P < &1 / &2 /\ --(lx * Q - hy * P) < &1 / &2)
        ==> abs(X * P + Y * Q) < &1 / &2 /\ abs(X * Q - Y * P) < &1 / &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`lx:real`; `hx:real`; `ly:real`; `hy:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`P:real`; `X:real`; `lx:real`; `hx:real`] BILIN) THEN
  MP_TAC(SPECL [`Q:real`; `X:real`; `lx:real`; `hx:real`] BILIN) THEN
  MP_TAC(SPECL [`P:real`; `Y:real`; `ly:real`; `hy:real`] BILIN) THEN
  MP_TAC(SPECL [`Q:real`; `Y:real`; `ly:real`; `hy:real`] BILIN) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CORE0 = prove
 (`forall r e P Q X Y.
        &0 < r /\ r * r = &2 /\ &0 < e /\ e <= &1 / &100 /\
        &0 <= P /\ &0 <= Q /\ P * P + Q * Q = &1 /\
        ((--(r / &4 - e / &4) <= X /\ X <= &1 - e / &4 - (P + Q) / &2) \/
         (--(&1 - e / &4 - (P + Q) / &2) <= X /\ X <= r / &4 - e / &4)) /\
        ((--(r / &4 - e / &4) <= Y /\ Y <= &1 - e / &4 - (P + Q) / &2) \/
         (--(&1 - e / &4 - (P + Q) / &2) <= Y /\ Y <= r / &4 - e / &4))
        ==> abs(X * P + Y * Q) < &1 / &2 /\ abs(X * Q - Y * P) < &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `e:real`; `P:real`; `Q:real`] BASIC5) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CORE_LIN THEN ASM_REWRITE_TAC[] THEN
  FIRST (map (fun l -> MAP_EVERY EXISTS_TAC l THEN ASM_REAL_ARITH_TAC)
   [[`--(r / &4 - e / &4)`; `&1 - e / &4 - (P + Q) / &2`;
     `--(r / &4 - e / &4)`; `&1 - e / &4 - (P + Q) / &2`];
    [`--(r / &4 - e / &4)`; `&1 - e / &4 - (P + Q) / &2`;
     `--(&1 - e / &4 - (P + Q) / &2)`; `r / &4 - e / &4`];
    [`--(&1 - e / &4 - (P + Q) / &2)`; `r / &4 - e / &4`;
     `--(r / &4 - e / &4)`; `&1 - e / &4 - (P + Q) / &2`];
    [`--(&1 - e / &4 - (P + Q) / &2)`; `r / &4 - e / &4`;
     `--(&1 - e / &4 - (P + Q) / &2)`; `r / &4 - e / &4`]]));;

let CORE = prove
 (`forall r e u1 u2 X Y.
        &0 < r /\ r * r = &2 /\ &0 < e /\ e <= &1 / &100 /\
        u1 * u1 + u2 * u2 = &1 /\
        ((--(r / &4 - e / &4) <= X /\
          X <= &1 - e / &4 - (abs u1 + abs u2) / &2) \/
         (--(&1 - e / &4 - (abs u1 + abs u2) / &2) <= X /\
          X <= r / &4 - e / &4)) /\
        ((--(r / &4 - e / &4) <= Y /\
          Y <= &1 - e / &4 - (abs u1 + abs u2) / &2) \/
         (--(&1 - e / &4 - (abs u1 + abs u2) / &2) <= Y /\
          Y <= r / &4 - e / &4))
        ==> abs(X * u1 + Y * u2) < &1 / &2 /\
            abs(--(X * u2) + Y * u1) < &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= u1` THEN ASM_CASES_TAC `&0 <= u2` THENL
   [MP_TAC(SPECL [`r:real`; `e:real`; `u1:real`; `u2:real`;
                  `X:real`; `Y:real`] CORE0);
    MP_TAC(SPECL [`r:real`; `e:real`; `u1:real`; `--u2`;
                  `X:real`; `--Y`] CORE0);
    MP_TAC(SPECL [`r:real`; `e:real`; `--u1`; `u2:real`;
                  `--X`; `Y:real`] CORE0);
    MP_TAC(SPECL [`r:real`; `e:real`; `--u1`; `--u2`;
                  `--X`; `--Y`] CORE0)] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]));;

(* The key lemma, with the square given by its centre and direction u.       *)

let KEY5U = prove
 (`forall r e s c1 c2 u1 u2.
        &0 < r /\ r * r = &2 /\ &0 < e /\ e <= &1 / &100 /\
        s = &2 + r / &2 - e /\ u1 * u1 + u2 * u2 = &1 /\
        (abs u1 + abs u2) / &2 <= c1 /\ c1 <= s - (abs u1 + abs u2) / &2 /\
        (abs u1 + abs u2) / &2 <= c2 /\ c2 <= s - (abs u1 + abs u2) / &2
        ==> exists z1 z2. (z1 = &1 - e / &4 \/ z1 = &1 + r / &2 - &3 * e / &4) /\
                    (z2 = &1 - e / &4 \/ z2 = &1 + r / &2 - &3 * e / &4) /\
                    abs((z1 - c1) * u1 + (z2 - c2) * u2) < &1 / &2 /\
                    abs(--((z1 - c1) * u2) + (z2 - c2) * u1) < &1 / &2`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `if c1 <= s / &2 then &1 - e / &4 else &1 + r / &2 - &3 * e / &4` THEN
  EXISTS_TAC `if c2 <= s / &2 then &1 - e / &4 else &1 + r / &2 - &3 * e / &4` THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CORE THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `e:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let KEY5 = prove
 (`forall r e s p1 p2 u1 u2 w1 w2.
        &0 < r /\ r * r = &2 /\ &0 < e /\ e <= &1 / &100 /\
        s = &2 + r / &2 - e /\
        u1 * u1 + u2 * u2 = &1 /\ w1 * w1 + w2 * w2 = &1 /\
        u1 * w1 + u2 * w2 = &0 /\
        &0 <= p1 /\ p1 <= s /\ &0 <= p2 /\ p2 <= s /\
        &0 <= p1 + u1 /\ p1 + u1 <= s /\ &0 <= p2 + u2 /\ p2 + u2 <= s /\
        &0 <= p1 + w1 /\ p1 + w1 <= s /\ &0 <= p2 + w2 /\ p2 + w2 <= s /\
        &0 <= p1 + u1 + w1 /\ p1 + u1 + w1 <= s /\
        &0 <= p2 + u2 + w2 /\ p2 + u2 + w2 <= s
        ==> exists z1 z2. (z1 = &1 - e / &4 \/ z1 = &1 + r / &2 - &3 * e / &4) /\
                    (z2 = &1 - e / &4 \/ z2 = &1 + r / &2 - &3 * e / &4) /\
                    &0 < (z1 - p1) * u1 + (z2 - p2) * u2 /\
                    (z1 - p1) * u1 + (z2 - p2) * u2 < &1 /\
                    &0 < (z1 - p1) * w1 + (z2 - p2) * w2 /\
                    (z1 - p1) * w1 + (z2 - p2) * w2 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `e:real`; `s:real`;
                `p1 + (u1 + w1) / &2`; `p2 + (u2 + w2) / &2`;
                `u1:real`; `u2:real`] KEY5U) THEN
  MP_TAC(SPECL [`u1:real`; `u2:real`; `w1:real`; `w2:real`] W_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lower bound.                                                          *)
(* ------------------------------------------------------------------------- *)

let SQRT2_FACTS = prove
 (`&0 < sqrt(&2) /\ sqrt(&2) * sqrt(&2) = &2`,
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH]);;

let CARD_LE_4 = prove
 (`forall a b c d:A. CARD {a,b,c,d} <= 4`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN ARITH_TAC);;

let NO_PACK5 = prove
 (`forall e. &0 < e /\ e <= &1 / &100 ==> ~packs 5 (&2 + sqrt(&2) / &2 - e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[packs]) THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:num->real^2->bool`
   (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "dis"))) THEN
  ABBREV_TAC `a = &1 - e / &4` THEN
  ABBREV_TAC `b = &1 + sqrt(&2) / &2 - &3 * e / &4` THEN
  SUBGOAL_THEN
   `forall i. i < 5
        ==> exists z. z IN {vector[a;a], vector[a;b], vector[b;a], vector[b;b]:real^2} /\
                z IN interior((sq:num->real^2->bool) i)`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "in" (MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[ASSUME `i < 5`] THEN
    REWRITE_TAC[UNIT_SQUARE_BOX; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:real^2`; `u:real^2`; `w:real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^2`; `u:real^2`; `w:real^2`] SQBOX_CORNERS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`sqrt(&2)`; `e:real`; `&2 + sqrt(&2) / &2 - e`;
                  `(p:real^2)$1`; `(p:real^2)$2`; `(u:real^2)$1`; `(u:real^2)$2`;
                  `(w:real^2)$1`; `(w:real^2)$2`] KEY5) THEN
    REWRITE_TAC[SQRT2_FACTS] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_binary "SUBSET" (concl th) then
        MAP_EVERY (fun t -> MP_TAC(SPEC t (REWRITE_RULE[SUBSET] th)))
          [`p:real^2`; `p + u:real^2`; `p + w:real^2`; `p + u + w:real^2`]
        else failwith "") THEN
      ASM_REWRITE_TAC[IN_CONTAINER; VECTOR_ADD_COMPONENT] THEN
      UNDISCH_TAC `(u:real^2) dot u = &1` THEN
      UNDISCH_TAC `(w:real^2) dot w = &1` THEN
      UNDISCH_TAC `(u:real^2) dot w = &0` THEN REWRITE_TAC[DOT_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z1:real`; `z2:real`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    EXISTS_TAC `vector[z1;z2]:real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC IN_INTERIOR_SQBOX THEN
    ASM_REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT; VECTOR_2];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num->real^2`) THEN
  MP_TAC(ISPECL [`5`; `z:num->real^2`;
                 `{vector[a;a], vector[a;b], vector[b;a], vector[b;b]:real^2}`]
                PIGEONHOLE_POINTS) THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY;
               ARITH_RULE `n <= 4 ==> n < 5`; CARD_LE_4] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  USE_THEN "dis" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `(z:num->real^2) j`) THEN ASM_MESON_TAC[]);;

let LOWER5 = prove
 (`forall t. packs 5 t ==> &2 + sqrt(&2) / &2 <= t`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPEC `min (&2 + sqrt(&2) / &2 - t) (&1 / &100)` NO_PACK5) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN DISCH_TAC THEN
  MATCH_MP_TAC PACKS_MONO THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Goebel's packing.                                                         *)
(* ------------------------------------------------------------------------- *)

let goebel_sq = new_definition
 `goebel_sq r i =
    if i = 0 then sqbox (vector[&0; &0]) (vector[&1; &0]) (vector[&0; &1])
    else if i = 1 then
      sqbox (vector[&1 + r / &2; &0]) (vector[&1; &0]) (vector[&0; &1])
    else if i = 2 then
      sqbox (vector[&0; &1 + r / &2]) (vector[&1; &0]) (vector[&0; &1])
    else if i = 3 then
      sqbox (vector[&1 + r / &2; &1 + r / &2]) (vector[&1; &0]) (vector[&0; &1])
    else sqbox (vector[&1 + r / &4; &1 - r / &4])
               (vector[r / &2; r / &2]) (vector[--(r / &2); r / &2])`;;

let SCALE_R = prove
 (`forall r y A. &0 < r /\ r * r = &2 /\ y = r / &2 * A /\ &0 <= y /\ y <= &1
           ==> &0 <= A /\ A <= r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `A = r * y` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `r * r = &2` THEN CONV_TAC REAL_FIELD;
    MP_TAC(SPECL [`r:real`; `y:real`; `&0`; `&1`] BILIN) THEN
    ASM_REAL_ARITH_TAC]);;

let GOEBEL_MEM = prove
 (`forall r x:real^2.
        &0 < r /\ r * r = &2
        ==> (x IN goebel_sq r 0
             ==> &0 <= x$1 /\ x$1 <= &1 /\ &0 <= x$2 /\ x$2 <= &1) /\
            (x IN goebel_sq r 1
             ==> &1 + r / &2 <= x$1 /\ x$1 <= &2 + r / &2 /\
                 &0 <= x$2 /\ x$2 <= &1) /\
            (x IN goebel_sq r 2
             ==> &0 <= x$1 /\ x$1 <= &1 /\
                 &1 + r / &2 <= x$2 /\ x$2 <= &2 + r / &2) /\
            (x IN goebel_sq r 3
             ==> &1 + r / &2 <= x$1 /\ x$1 <= &2 + r / &2 /\
                 &1 + r / &2 <= x$2 /\ x$2 <= &2 + r / &2) /\
            (x IN goebel_sq r 4
             ==> &2 <= x$1 + x$2 /\ x$1 + x$2 <= &2 + r /\
                 --(r / &2) <= x$2 - x$1 /\ x$2 - x$1 <= r / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[goebel_sq; ARITH_EQ; sqbox; IN_ELIM_THM; DOT_2;
              VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  REPEAT CONJ_TAC THEN TRY(REAL_ARITH_TAC) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `((x:real^2)$1 - (&1 + r / &4)) * r / &2 +
                           ((x:real^2)$2 - (&1 - r / &4)) * r / &2`;
                `(x:real^2)$1 + x$2 - &2`] SCALE_R) THEN
  MP_TAC(SPECL [`r:real`; `((x:real^2)$1 - (&1 + r / &4)) * --(r / &2) +
                           ((x:real^2)$2 - (&1 - r / &4)) * r / &2`;
                `(x:real^2)$2 - x$1 + r / &2`] SCALE_R) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC]) THEN
  ASM_REAL_ARITH_TAC);;

let GOEBEL_MEMS =
  let th = UNDISCH(SPEC_ALL GOEBEL_MEM) in
  map (fun c -> GENL [`r:real`; `x:real^2`] (DISCH_ALL c)) (CONJUNCTS th);;

let GOEBEL_SEP_TAC a b =
  MATCH_MP_TAC DISJOINT_INTERIORS_SEPARATED THEN
  MAP_EVERY EXISTS_TAC [a; b] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT; DOT_2] THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`r:real`; `x:real^2`] th)) GOEBEL_MEMS THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(fun th -> if is_imp(concl th) then ALL_TAC
                              else STRIP_ASSUME_TAC th)) THEN
  ASM_REAL_ARITH_TAC;;

let LT5_CASES = ARITH_RULE `i < 5 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4`;;

let GOEBEL_DISJOINT = prove
 (`forall r. &0 < r /\ r * r = &2
       ==> forall i j. i < 5 /\ j < 5 /\ ~(i = j)
                 ==> DISJOINT (interior(goebel_sq r i)) (interior(goebel_sq r j))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `forall i j. i < 5 /\ j < 5 /\ i < j
          ==> DISJOINT (interior(goebel_sq r i)) (interior(goebel_sq r j))`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(i:num = j) ==> i < j \/ j < i`)) THEN
    ASM_MESON_TAC[DISJOINT_SYM]] THEN
  REWRITE_TAC[IMP_CONJ; LT5_CASES] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC(LAND_CONV NUM_LT_CONV) THEN REWRITE_TAC[]
  THENL
   [GOEBEL_SEP_TAC `vector[&1; &0]:real^2` `&1`;
    GOEBEL_SEP_TAC `vector[&0; &1]:real^2` `&1`;
    GOEBEL_SEP_TAC `vector[&1; &0]:real^2` `&1`;
    GOEBEL_SEP_TAC `vector[&1; &1]:real^2` `&2`;
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    GOEBEL_SEP_TAC `vector[&1; &0]:real^2` `&1`;
    GOEBEL_SEP_TAC `vector[&0; &1]:real^2` `&1`;
    GOEBEL_SEP_TAC `vector[-- &1; &1]:real^2` `--(r / &2)`;
    GOEBEL_SEP_TAC `vector[&1; &0]:real^2` `&1`;
    GOEBEL_SEP_TAC `vector[&1; -- &1]:real^2` `--(r / &2)`;
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    GOEBEL_SEP_TAC `vector[&1; &1]:real^2` `&2 + r`]);;

let GOEBEL_PACKS = prove
 (`forall r. &0 < r /\ r * r = &2 ==> packs 5 (&2 + r / &2)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[packs] THEN
  EXISTS_TAC `goebel_sq r` THEN ASM_SIMP_TAC[GOEBEL_DISJOINT] THEN
  REWRITE_TAC[LT5_CASES] THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[goebel_sq; ARITH_EQ] THEN MATCH_MP_TAC BOX_IMP_UNIT_SQUARE THEN
     REWRITE_TAC[DOT_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[SUBSET; IN_CONTAINER] THEN X_GEN_TAC `x:real^2` THEN
     DISCH_TAC THEN
     MAP_EVERY (fun th -> MP_TAC(SPECL [`r:real`; `x:real^2`] th)) GOEBEL_MEMS THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT(DISCH_THEN(fun th -> if is_imp(concl th) then ALL_TAC
                                 else STRIP_ASSUME_TAC th)) THEN
     MP_TAC(SPEC `r:real` R2_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Main theorems.                                                            *)
(* ------------------------------------------------------------------------- *)

let PACKS_5 = prove
 (`forall t. packs 5 t <=> &2 + sqrt(&2) / &2 <= t`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[LOWER5] THEN DISCH_TAC THEN
  MATCH_MP_TAC PACKS_MONO THEN EXISTS_TAC `&2 + sqrt(&2) / &2` THEN
  ASM_SIMP_TAC[GOEBEL_PACKS; SQRT2_FACTS]);;

let SQUARE_PACKING_SIDE_5 = prove
 (`square_packing_side 5 = &2 + sqrt(&2) / &2`,
  REWRITE_TAC[square_packing_side; PACKS_5] THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]);;
