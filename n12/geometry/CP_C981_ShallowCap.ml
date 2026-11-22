(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShallowCap.lean                            *)
(* (N12Compact.C981CompletionShallowCap).  The shallow circular cap in C981   *)
(* row 71.  OpenSquare q is (c,s,u,v,a) with c*c+s*s = 1 and 0 < a;          *)
(* inside_segment is CES_INSIDE_SEGMENT, short_projections is                *)
(* WFP_SHORT_PROJECTIONS, affine_endpoint_nonnegative is                     *)
(* SCAP_AFFINE_ENDPOINT_NONNEG and inside_iff_rotated_box is TSS_INSIDE_FACE.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_TopReach.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let C981SC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C981SC_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981SC_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: Cap *)
let c981sc_cap = new_definition
 `c981sc_cap x y <=>
    --(&13 / &50) <= x /\ x <= &0 /\ --(&69 / &2000) <= y /\ y <= &0 /\
    (x + &13 / &50) pow 2 + (y + &1) pow 2 <= &1`;;

(* Lean: arc828 *)
let C981SC_ARC828 = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&207 / &250) * c * s <= c + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c + s <= &283 / &200` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&283 / &200 * &283 / &200 < (c + s) * (c + s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `c - s:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981SC_PROD `&0 <= (c + s - &1) * (&283 / &200 - (c + s))` THEN
  C981SC_PROD `&0 <= c * s` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: left_support (private) *)
let C981SC_LEFT_SUPPORT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a (&0) (--(&37 / &50)) /\
     (forall y. ~linside c s u v a (--(&1)) y)
     ==> --(&1) <= c * u - s * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall x y. linside c s u v a x y ==> --(&1) <= x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `exists t. &0 <= t /\ t <= &1 /\ t * x = x + &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(--x - &1) / --x` THEN
    SUBGOAL_THEN `&0 < --x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `t * --x = --x - &1 ==> t * x = x + &1`) THEN
     MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`;
                 `&0`; `--(&37 / &50)`; `t:real`] CES_INSIDE_SEGMENT) THEN
   SUBGOAL_THEN `(&1 - t) * x + t * &0 = --(&1)` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= c * u - s * (v + a) + &1 ==> --(&1) <= c * u - s * (v + a)`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + e) - s * (v + a - e)`;
                                `s * (u + e) + c * (v + a - e)`]) THEN
  ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: positive_tip *)
let C981SC_POSITIVE_TIP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     linside c s u v a (&0) (--(&37 / &50)) /\
     ~linside c s u v a (&0) (&0) /\
     ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
     (forall y. --(&37 / &50) <= y /\ y <= --(&1 / &5) ==> ~linside c s u v a (--(&1)) y)
     ==> linside c s u v a (--(&3 / &100)) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal c s` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; ALL_TAC] THEN
  C981SC_UNFOLD_TAC `linside c s u v a (--(&13 / &50)) (&0)` THEN
  C981SC_UNFOLD_TAC `linside c s u v a (&0) (--(&37 / &50))` THEN
  SUBGOAL_THEN `u + a <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&0) (&0)` THEN REWRITE_TAC[linside] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981WS_CANONICAL_PROJECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&13 / &50 * s - c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (--(&13 / &50)) (--(&1))` THEN REWRITE_TAC[linside] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a /\ c /\ d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL [ALL_TAC; DISCH_TAC THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&97 / &100`; `&1 / &5`] WFP_SHORT_PROJECTIONS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `--(&37 / &50)`; `&13 / &50`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v + a <= s - &1 / &5 * c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `--(&1 / &5)` o check (is_forall o concl)) THEN
   REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `--c - &37 / &50 * s <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `--(&37 / &50)` o check (is_forall o concl)) THEN
   REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `forall y. ~linside c s u v a (--(&1)) y` ASSUME_TAC THENL
  [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
   C981SC_UNFOLD_TAC `linside c s u v a (--(&1)) y` THEN
   SUBGOAL_THEN `--(&37 / &50) < y` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < y + &37 / &50 ==> --(&37 / &50) < y`) THEN
    MATCH_MP_TAC C981SC_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `y < --(&1 / &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < --(&1 / &5) - y ==> y < --(&1 / &5)`) THEN
    MATCH_MP_TAC C981SC_POS_OF_MUL THEN EXISTS_TAC `c:real` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981SC_LEFT_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981SC_ARC828) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C981SC_PROD `&0 <= c * (--(&3 / &100) * c - (u + a))` THEN
  C981SC_PROD `&0 <= s * (v - (&13 / &50 * s - c))` THEN
  C981SC_PROD `&0 <= (c - &43 / &15 * s) * (c - &43 / &15 * s)` THEN
  C981SC_PROD `&0 < s * s` THEN
  C981SC_PROD `&0 < (a - &1) * (c + s)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_cap *)
let C981SC_NEGATIVE_CAP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     linside c s u v a (&0) (--(&37 / &50)) /\
     ~linside c s u v a (--(&13 / &50)) (--(&1))
     ==> forall x y. c981sc_cap x y ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C981SC_UNFOLD_TAC `linside c s u v a (--(&13 / &50)) (&0)` THEN
  C981SC_UNFOLD_TAC `linside c s u v a (&0) (--(&37 / &50))` THEN
  SUBGOAL_THEN `&13 / &50 * s - c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (--(&13 / &50)) (--(&1))` THEN REWRITE_TAC[linside] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[c981sc_cap; REAL_POW_2] THEN STRIP_TAC THEN
  C981SC_PROD `&0 <= c * (x + &13 / &50)` THEN
  C981SC_PROD `&0 <= --s * --y` THEN
  C981SC_PROD `&0 <= c * --x` THEN
  C981SC_PROD `&0 <= --s * (y + &37 / &50)` THEN
  C981SC_PROD `&0 <= --s * (x + &13 / &50)` THEN
  C981SC_PROD `&0 <= c * (y + &69 / &2000)` THEN
  SUBGOAL_THEN `--s * (x + &13 / &50) + c * (y + &1) <= &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `(--s * (x + &13 / &50) + c * (y + &1)) * (--s * (x + &13 / &50) + c * (y + &1)) +
                 (c * (x + &13 / &50) + s * (y + &1)) * (c * (x + &13 / &50) + s * (y + &1)) =
                 (x + &13 / &50) * (x + &13 / &50) + (y + &1) * (y + &1)` MP_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPEC `c * (x + &13 / &50) + s * (y + &1)` REAL_LE_SQUARE) THEN
   UNDISCH_TAC `(x + &13 / &50) * (x + &13 / &50) + (y + &1) * (y + &1) <= &1` THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`--s * (x + &13 / &50) + c * (y + &1)`,`X:real`) THEN
   SPEC_TAC(`(c * (x + &13 / &50) + s * (y + &1)) * (c * (x + &13 / &50) + s * (y + &1))`,
            `Y:real`) THEN
   SPEC_TAC(`(x + &13 / &50) * (x + &13 / &50) + (y + &1) * (y + &1)`,`N:real`) THEN
   REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&1 * &1 < X * X` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC);;
