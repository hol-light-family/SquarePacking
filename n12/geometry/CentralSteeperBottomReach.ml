(* ========================================================================= *)
(* Port of Compact/Geometry/CentralSteeperBottomReach.lean (Jatloe,          *)
(* N12-jatloe; namespace N12Compact.CentralSteeperBottomReach).  The actual  *)
(* bottom wall occupies both 2.4 and 2.6 on the row y = 1; those two points  *)
(* rule out the reversed positive incoming-axis escape.  Normal is           *)
(* c977cc_normal; lower is ABT_lower, lower_in_bands C977NCO_LOWER_IN_BANDS. *)
(* Lean Normal C (-S) is c977cc_normal C (--S).  The Lean local              *)
(* abbreviations X, Y are variables with their defining equations; K, H are  *)
(* written out.  The OpenSquare invariants are explicit hypotheses.          *)
(* Tag CSBR_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let CSBR_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CSBR_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

let CSBR_SPLIT_TAC =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* the lower support when K = nx c + ny s >= 0 >= H = ny c - nx s (Lean formula) *)
let CSBR_LOWER_PN = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ ny * c - nx * s <= &0
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * u + (ny * c - nx * s) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `--nx * s + ny * c = ny * c - nx * s`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

(* the final support comparison shared by both lower_v lemmas:
   lower = K u + H (v + a) <= K (3c + 2s - 1) + H (c - x s + 1) *)
let CSBR_SUPPORT = prove
 (`forall c s u v a C S x.
     &0 <= C * c + S * s /\ S * c - C * s <= &0 /\ &1 <= a /\
     u + a <= &3 * c + &2 * s /\ c - x * s <= v
     ==> ABT_lower c s u v a C S <=
         (C * c + S * s) * (&3 * c + &2 * s - &1) + (S * c - C * s) * (c - x * s + &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CSBR_LOWER_PN] THEN
  CSBR_PROD_TAC `C * c + S * s` `(&3 * c + &2 * s) - (u + a)` THEN
  CSBR_PROD_TAC `--(S * c - C * s)` `v - (c - x * s)` THEN
  CSBR_PROD_TAC `(C * c + S * s) - (S * c - C * s)` `a - &1` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lower_v_impossible (private) *)
let CSBR_LOWER_V_IMPOSSIBLE = prove
 (`forall c s u v a C S x.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c s /\ &1 <= a /\ S * c <= C * s /\
     u + a <= &3 * c + &2 * s /\ &2 * (C + S) < ABT_lower c s u v a C S /\
     &1 - c - s + c * s + (x - &3) * s pow 2 <= &0
     ==> ~(c - x * s <= v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN CSBR_NORMAL_TAC THEN
  SUBGOAL_THEN `exists X. X = &1 - c - s + c * s + (x - &3) * s pow 2` (X_CHOOSE_TAC `X:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `exists Y. Y = c - c pow 2 - s + (&3 - x) * c * s` (X_CHOOSE_TAC `Y:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `X <= &0` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c * X + s * Y = c - &1` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `C * X + S * Y <= &0` ASSUME_TAC THENL
  [ASM_CASES_TAC `Y <= &0` THENL
   [CSBR_PROD_TAC `C:real` `--X` THEN CSBR_PROD_TAC `S:real` `--Y` THEN
    NLIN_TAC ~deg2:false [];
    CSBR_PROD_TAC `C:real` `&1 - c` THEN
    CSBR_PROD_TAC `C * s - S * c` `Y:real` THEN
    SUBGOAL_THEN `c * (C * X + S * Y) = C * (c - &1) - (C * s - S * c) * Y` ASSUME_TAC THENL
    [UNDISCH_TAC `c * X + s * Y = c - &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `c * (C * X + S * Y) <= &0` ASSUME_TAC THENL
    [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `C * X + S * Y`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `C:real`; `S:real`; `x:real`]
    CSBR_SUPPORT) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(C * c + S * s) * (&3 * c + &2 * s - &1) + (S * c - C * s) * (c - x * s + &1) -
    &2 * (C + S) = C * X + S * Y` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: missing_lower_faces (private) *)
let CSBR_MISSING_LOWER_FACES = prove
 (`forall c s u v a x.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\
     &12 / &5 <= x /\ x <= &13 / &5 /\
     linside c s u v a (&3) (&87 / &50) /\ ~linside c s u v a x (&1)
     ==> x * c + s <= u \/ c - x * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CSBR_NORMAL_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME `linside c s u v a (&3) (&87 / &50)`)) THEN
  CSBR_PROD_TAC `c:real` `&3 - x` THEN
  SUBGOAL_THEN `x * c + s < u + a` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CSBR_PROD_TAC `s:real` `x - &12 / &5` THEN
  SUBGOAL_THEN `c - x * s < v + a` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `x * c + s <= u` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a x (&1)` THEN
  REWRITE_TAC[linside; TAUT `(~p ==> false) <=> p`] THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* firstHorizontal / lastHorizontal *)
let CSBR_FIRST_HORIZONTAL = prove
 (`forall c s. c977cc_normal c s ==> &1 - c - s + c * s + (&12 / &5 - &3) * s pow 2 <= &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CSBR_NORMAL_TAC THEN
  CSBR_PROD_TAC `&1 - c` `(&3 / &5) * c + s - &2 / &5` THEN
  SUBGOAL_THEN `&1 - c - s + c * s + (&12 / &5 - &3) * s pow 2 =
                (&1 - c) * (&2 / &5 - (&3 / &5) * c - s)` SUBST1_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

let CSBR_LAST_HORIZONTAL = prove
 (`forall c s. c977cc_normal c s /\ &2 / &5 < s
         ==> &1 - c - s + c * s + (&13 / &5 - &3) * s pow 2 <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CSBR_NORMAL_TAC THEN
  CSBR_PROD_TAC `&1 - c` `(&2 / &5) * c + s - &3 / &5` THEN
  SUBGOAL_THEN `&1 - c - s + c * s + (&13 / &5 - &3) * s pow 2 =
                (&1 - c) * (&3 / &5 - (&2 / &5) * c - s)` SUBST1_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* short: (2/5) c + s < 1 *)
let CSBR_SHORT = prove
 (`forall c s. c977cc_normal c s ==> (&2 / &5) * c + s < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CSBR_NORMAL_TAC THEN
  SUBGOAL_THEN `(c + s) pow 2 <= &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * c + s <= (&7 / &10) * (c + s)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; NLIN_TAC []]);;

(* the common skeleton of impossible / negative_impossible, given the lower_v lemma *)
let CSBR_CLOSE_TAC lowv =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CSBR_FIRST_HORIZONTAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&12 / &5`]
    CSBR_MISSING_LOWER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC THENL
  [ALL_TAC;
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `C:real`; `S:real`; `&12 / &5`]
     lowv) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC] THEN
  CSBR_NORMAL_TAC THEN
  SUBGOAL_THEN `&2 / &5 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CSBR_LAST_HORIZONTAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CSBR_SHORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&13 / &5`]
    CSBR_MISSING_LOWER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC THENL
  [ASM_REAL_ARITH_TAC;
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `C:real`; `S:real`; `&13 / &5`]
     lowv) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];;

(* Lean: impossible *)
let CSBR_IMPOSSIBLE = prove
 (`forall c s u v a C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c s /\ &1 < a /\ S * c <= C * s /\
     u + a <= &3 * c + &2 * s /\ &2 * (C + S) < ABT_lower c s u v a C S /\
     linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&12 / &5) (&1) /\ ~linside c s u v a (&13 / &5) (&1)
     ==> false`,
  CSBR_CLOSE_TAC CSBR_LOWER_V_IMPOSSIBLE);;

(* Lean: negative_lower_v_impossible (private) *)
let CSBR_NEGATIVE_LOWER_V_IMPOSSIBLE = prove
 (`forall c s u v a C S x.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C (--S) /\ c977cc_normal c s /\ x <= &13 / &5 /\ &1 <= a /\
     u + a <= &3 * c + &2 * s /\ &2 * C + (&3 / &2) * S < ABT_lower c s u v a C S /\
     &1 - c - s + c * s + (x - &3) * s pow 2 <= &0
     ==> ~(c - x * s <= v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN CSBR_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_NEG; ARITH]) THEN
  SUBGOAL_THEN `exists X. X = &1 - c - s + c * s + (x - &3) * s pow 2` (X_CHOOSE_TAC `X:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `exists Y. Y = c - c pow 2 - s + (&3 - x) * c * s` (X_CHOOSE_TAC `Y:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `X <= &0` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CSBR_PROD_TAC `c:real` `C + S` THEN CSBR_PROD_TAC `--S` `c - s` THEN
  SUBGOAL_THEN `&0 <= C * c + S * s` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CSBR_PROD_TAC `--S` `c:real` THEN CSBR_PROD_TAC `C:real` `s:real` THEN
  SUBGOAL_THEN `S * c - C * s <= &0` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c * s <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  CSBR_PROD_TAC `&3 / &10 - (&1 - c)` `&3 / &10 + (&1 - c)` THEN
  SUBGOAL_THEN `(&1 - c) pow 2 <= &9 / &100` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CSBR_PROD_TAC `c * s` `&13 / &5 - x` THEN
  MP_TAC(SPECL [`s pow 2`; `&13 / &5 - x`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `X - Y - &1 / &2 <= &0` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false [SPEC `s:real` REAL_LE_POW_2]; ALL_TAC] THEN
  CSBR_PROD_TAC `C + S` `--X` THEN
  CSBR_PROD_TAC `--S` `--(X - Y - &1 / &2)` THEN
  SUBGOAL_THEN `C * X + S * (Y + &1 / &2) <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `C:real`; `S:real`; `x:real`]
    CSBR_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(C * c + S * s) * (&3 * c + &2 * s - &1) + (S * c - C * s) * (c - x * s + &1) -
    (&2 * C + (&3 / &2) * S) = C * X + S * (Y + &1 / &2)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_impossible *)
let CSBR_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C (--S) /\ c977cc_normal c s /\ &1 < a /\
     u + a <= &3 * c + &2 * s /\ &2 * C + (&3 / &2) * S < ABT_lower c s u v a C S /\
     linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&12 / &5) (&1) /\ ~linside c s u v a (&13 / &5) (&1)
     ==> false`,
  CSBR_CLOSE_TAC CSBR_NEGATIVE_LOWER_V_IMPOSSIBLE);;
