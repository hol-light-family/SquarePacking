(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShallowWall.lean                           *)
(* (N12Compact.C981CompletionShallowWall).  The top-wall reach in the        *)
(* presence of the actual foreign circular cap.  Cap is c981sc_cap; arc828   *)
(* is C981SC_ARC828; upper_wall is C981CA_UPPER_WALL; short_projections is   *)
(* WFP_SHORT_PROJECTIONS; canonical_frame is CLF_CANONICAL_FRAME.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_ShallowCap.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C981SW_LIN = NLIN_TAC ~deg2:false [];;

let C981SW_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C981SW_LIN; ALL_TAC];;

let C981SW_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C981SW_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981SW_LIN; ALL_TAC];;

let C981SW_avoid = `forall x y. c981sc_cap x y ==> ~linside c s u v a x y`;;

(* contradiction from a cap point (x,y) (cap theorem capth) inside the square *)
let C981SW_AVOID_TAC capth =
  let x = rand(rator(concl capth)) and y = rand(concl capth) in
  SUBGOAL_THEN (list_mk_comb(`linside c s u v a`, [x; y])) MP_TAC THENL
   [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981SW_LIN; ALL_TAC] THEN
  MP_TAC(MP (SPECL [x; y] (ASSUME C981SW_avoid)) capth) THEN CONV_TAC TAUT;;

let C981SW_CAP x y =
  prove(list_mk_comb(`c981sc_cap`, [x; y]),
        REWRITE_TAC[c981sc_cap] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let C981SW_CAPF = C981SW_CAP `--(&13 / &50)` `&0`;;
let C981SW_CAPY = C981SW_CAP `&0` `--(&69 / &2000)`;;
let C981SW_CAPZ = C981SW_CAP `--(&1 / &5)` `--(&1 / &500)`;;

let C981SW_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID] THEN STRIP_TAC;;

(* Lean: negative_wall (private) *)
let C981SW_NEGATIVE_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
               (forall x y. linside c s u v a x y ==> y <= &1)
               ==> s * u + c * (v + a) <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real` THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: positive (private) *)
let C981SW_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     (forall x y. c981sc_cap x y ==> ~linside c s u v a x y)
     ==> linside c s u v a (&73 / &100) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal c s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981SC_ARC828) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&73 / &100`; `&69 / &2000`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C981SW_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981SW_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  C981SW_PROD `&0 <= c * s` THEN
  C981SW_PROD `&0 < (a - &1) * (c + s)` THEN
  SUBGOAL_THEN `(&73 / &100) * c < u + a` ASSUME_TAC THENL
   [C981SW_CONTRA THEN
    SUBGOAL_THEN `v + a <= (&13 / &50) * s` ASSUME_TAC THENL
     [C981SW_CONTRA THEN C981SW_AVOID_TAC C981SW_CAPF;
      ALL_TAC] THEN
    C981SW_AVOID_TAC C981SW_CAPY;
    ALL_TAC] THEN
  SUBGOAL_THEN `v < --(&73 / &100) * s` ASSUME_TAC THENL
   [C981SW_CONTRA THEN
    SUBGOAL_THEN `--(&13 / &50) * c <= u` ASSUME_TAC THENL
     [C981SW_CONTRA THEN C981SW_AVOID_TAC C981SW_CAPF;
      ALL_TAC] THEN
    C981SW_PROD `&0 <= s * (u + (&13 / &50) * c)` THEN
    C981SW_PROD `&0 <= c * (v + (&73 / &100) * s)` THEN
    C981SW_FACT `a * (c + s) <= &1 + (&99 / &100) * c * s` THEN
    SUBGOAL_THEN `&2 / &99 < s` ASSUME_TAC THENL
     [C981SW_CONTRA THEN
      C981SW_PROD `&0 <= (c + s - &1) * (&101 / &99 - (c + s))` THEN
      C981SW_LIN;
      ALL_TAC] THEN
    C981SW_PROD `&0 <= s * (c - s)` THEN
    SUBGOAL_THEN `u < --(&69 / &2000) * s` ASSUME_TAC THENL
     [C981SW_CONTRA THEN
      C981SW_PROD `&0 <= s * (u + (&69 / &2000) * s)` THEN
      C981SW_LIN;
      ALL_TAC] THEN
    SUBGOAL_THEN `--(&69 / &2000) * c <= v` ASSUME_TAC THENL
     [C981SW_CONTRA THEN C981SW_AVOID_TAC C981SW_CAPY;
      ALL_TAC] THEN
    C981SW_PROD `&0 <= (c + s - &1) * (&869 / &800 - (c + s))` THEN
    C981SW_FACT `&1 + (&233 / &250) * c * s <= c + s` THEN
    SUBGOAL_THEN `u < --(&1 / &5) * c - (&1 / &500) * s` ASSUME_TAC THENL
     [C981SW_CONTRA THEN
      C981SW_PROD `&0 <= s * (u + (&1 / &5) * c + (&1 / &500) * s)` THEN
      C981SW_LIN;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / &5) * s - (&1 / &500) * c <= v` ASSUME_TAC THENL
     [C981SW_CONTRA THEN C981SW_AVOID_TAC C981SW_CAPZ;
      ALL_TAC] THEN
    C981SW_LIN;
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981SW_LIN);;

(* Lean: negative (private) *)
let C981SW_NEGATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     (forall x y. c981sc_cap x y ==> ~linside c s u v a x y)
     ==> linside c s u v a (&73 / &100) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal c (--s)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981SW_NEGATIVE_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&73 / &100`; `&69 / &2000`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C981SW_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981SW_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  C981SW_PROD `&0 < (a - &1) * (c + --s)` THEN
  SUBGOAL_THEN `--(&73 / &100) * s < v + a` ASSUME_TAC THENL
   [C981SW_CONTRA THEN C981SW_AVOID_TAC C981SW_CAPY;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&73 / &100) * c < u + a` ASSUME_TAC THENL
   [C981SW_CONTRA THEN
    (* capFaces *)
    SUBGOAL_THEN `forall x y. c981sc_cap x y ==> --s * x + c * y <= v` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c981sc_cap]) THEN
      C981SW_PROD `&0 <= c * (x + &13 / &50)` THEN
      C981SW_PROD `&0 <= --s * --y` THEN
      C981SW_PROD `&0 <= c * --x` THEN
      C981SW_PROD `&0 <= --s * (y + &69 / &2000)` THEN
      C981SW_PROD `&0 <= --s * --x` THEN
      C981SW_PROD `&0 <= c * --y` THEN
      C981SW_CONTRA THEN
      SUBGOAL_THEN `linside c s u v a x y` MP_TAC THENL
       [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981SW_LIN; ALL_TAC] THEN
      MP_TAC(MP (SPECL [`x:real`; `y:real`] (ASSUME C981SW_avoid))
                (ASSUME `c981sc_cap x y`)) THEN CONV_TAC TAUT;
      ALL_TAC] THEN
    C981SW_PROD `&0 <= --s * ((&73 / &100) * c - (u + a))` THEN
    C981SW_PROD `&0 <= c * --s` THEN
    ASM_CASES_TAC `--s <= &13 / &50` THENL
     [C981SW_PROD `&0 <= (&13 / &50 - --s) * (&13 / &50 + --s)` THEN
      SUBGOAL_THEN `&1931 / &2000 <= c` ASSUME_TAC THENL
       [C981SW_CONTRA THEN
        C981SW_PROD `&0 <= (&1931 / &2000 - c) * (&1931 / &2000 + c)` THEN C981SW_LIN;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`--s - &13 / &50`; `c - &1`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `v:real`)) (concl th) &&
                         not (can (find_term ((=) `linside`)) (concl th)))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[c981sc_cap] THEN REPEAT CONJ_TAC THEN TRY C981SW_LIN THEN
        REWRITE_TAC[REAL_ARITH `--s - &13 / &50 + &13 / &50 = --s`;
                    REAL_ARITH `c - &1 + &1 = c`; REAL_POW_2] THEN C981SW_LIN;
        DISCH_TAC] THEN
      C981SW_FACT `&1 - c - (&13 / &50) * --s <= v` THEN
      C981SW_PROD `&0 <= c * (v - (&1 - c - (&13 / &50) * --s))` THEN
      C981SW_PROD `&0 <= (&1 - c) * (--s - (&1 - c))` THEN
      C981SW_LIN;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `--(&69 / &2000)`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `v:real`)) (concl th) &&
                       not (can (find_term ((=) `linside`)) (concl th)))) THEN
    REWRITE_TAC[C981SW_CAPY] THEN DISCH_TAC THEN
    C981SW_PROD `&0 <= c * (v + (&69 / &2000) * c)` THEN
    C981SW_FACT `a * (c + --s) <= &1 + (&73 / &100) * c * --s + (&69 / &2000) * c * c` THEN
    C981SW_PROD `&0 < c * c` THEN
    ASM_CASES_TAC `--s < &1 / &3` THENL
     [C981SW_PROD `&0 <= --s * (&1 - c)` THEN
      SUBGOAL_THEN `c + --s <= &13 / &10` ASSUME_TAC THENL
       [NLIN_TAC [SQ_NONNEG `c + --s - &13 / &10`]; ALL_TAC] THEN
      C981SW_PROD `&0 <= (c + --s - &1) * (&13 / &10 - (c + --s))` THEN
      C981SW_FACT `&1 + (&20 / &23) * c * --s <= c + --s` THEN
      C981SW_PROD `&0 < c * (--s - (&13 / &50) * c)` THEN
      C981SW_LIN;
      ALL_TAC] THEN
    C981SW_PROD `&0 <= (--s - &1 / &3) * (--s + &1 / &3)` THEN
    SUBGOAL_THEN `(&353 / &1000) * c < --s` ASSUME_TAC THENL
     [C981SW_CONTRA THEN
      C981SW_PROD `&0 <= ((&353 / &1000) * c - --s) * ((&353 / &1000) * c + --s)` THEN
      C981SW_LIN;
      ALL_TAC] THEN
    C981SW_PROD `&0 < c * (--s - (&353 / &1000) * c)` THEN
    MP_TAC(SPECL [`c:real`; `--s`] C981SC_ARC828) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C981SW_LIN;
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981SW_LIN);;

(* Lean: point *)
let C981SW_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     (forall x y. c981sc_cap x y ==> ~linside c s u v a x y)
     ==> linside c s u v a (&73 / &100) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [MATCH_MP_TAC C981SW_POSITIVE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C981SW_NEGATIVE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN ASM_REAL_ARITH_TAC]);;
