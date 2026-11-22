(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C702SouthPoint.lean                 *)
(* (N12Compact.CommonCases.C702SouthPoint).  The southwest closing point of  *)
(* C702.  Avoid is ccc7sp_avoid; increasing_projection is                    *)
(* CCOS_INCREASING_PROJECTION; LowerSegmentSupport.support is CCLSS_SUPPORT; *)
(* short_projections is WFP_SHORT_PROJECTIONS; canonical_frame is            *)
(* CLF_CANONICAL_FRAME.  The Lean frame turn^3 o pullSwap is the 5-tuple     *)
(* (c, --s, v, u, a) (C702SP_SWAP).                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_C702SouthScalars.ml";;
needs "n12/geometry/CP_CommonCases_LowerSegmentSupport.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let CCC7SP_LIN = NLIN_TAC ~deg2:false [];;

let CCC7SP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   CCC7SP_LIN; ALL_TAC];;

let CCC7SP_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [CCC7SP_LIN; ALL_TAC];;

let CCC7SP_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* contradiction with an omitted point (theorem ~linside ...) *)
let CCC7SP_MISS_TAC th =
  MP_TAC th THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> false`) THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN CCC7SP_LIN;;

let CCC7SP_MISS t = CCC7SP_MISS_TAC (ASSUME t);;

let CCC7SP_UNFOLD_ALL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> can (term_match [] `linside c s u v a x y`) (concl th)) ths));;

let CCC7SP_ANTS = REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) ORELSE
   ASM_REAL_ARITH_TAC ORELSE CCC7SP_LIN);;

(* Lean: Avoid (private definition) *)
let ccc7sp_avoid = new_definition
 `ccc7sp_avoid (c:real) s u v a <=>
    forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (&41 / &20) + w * (&47 / &20))
                           ((&1 - w) * (&41 / &20) + w * (&33 / &20))`;;

let CCC7SP_AVOID_AT = prove
 (`forall c s u v a. ccc7sp_avoid c s u v a
     ==> ~linside c s u v a (&47 / &20) (&33 / &20) /\
         ~linside c s u v a (&41 / &20) (&41 / &20)`,
  REWRITE_TAC[ccc7sp_avoid] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`); FIRST_X_ASSUM(MP_TAC o SPEC `&0`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* Lean: positive_faces *)
let CCC7SP_POSITIVE_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&1) (&33 / &20) /\ ~linside c s u v a (&33 / &20) (&1) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> c + s * (&33 / &20) <= u /\ --s * (&33 / &20) + c <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCC7SP_UNFOLD_ALL_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&0`; `&27 / &20`] CCOS_INCREASING_PROJECTION)) THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&7 / &10`; `&7 / &10`] CCOS_INCREASING_PROJECTION)) THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&13 / &20`; `&13 / &20`] CCOS_INCREASING_PROJECTION)) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&7 / &10`; `&13 / &20`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--s * (&33 / &20) + c <= v` ASSUME_TAC THENL
   [CCC7SP_CONTRA THEN
    SUBGOAL_THEN `c * (&33 / &20) + s <= u` ASSUME_TAC THENL
     [CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&33 / &20) (&1)`; ALL_TAC] THEN
    SUBGOAL_THEN `v + a <= --s * (&33 / &20) + c * (&47 / &20)` ASSUME_TAC THENL
     [CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&33 / &20) (&47 / &20)`; ALL_TAC] THEN
    SUBGOAL_THEN `--s * (&47 / &20) + c * (&33 / &20) <= v` ASSUME_TAC THENL
     [CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&47 / &20) (&33 / &20)`; ALL_TAC] THEN
    CCC7SP_LIN;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&1) (&33 / &20)`);;

(* Lean: upper_support (private) *)
let CCC7SP_UPPER_SUPPORT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     u < c * (&47 / &20) + s * (&33 / &20) /\
     v < --s * (&47 / &20) + c * (&33 / &20) /\
     --s * (&47 / &20) + c * (&33 / &20) < v + a /\
     u < c * (&41 / &20) + s * (&41 / &20) /\
     v < --s * (&41 / &20) + c * (&41 / &20) /\
     ccc7sp_avoid c s u v a
     ==> u + a <= c * (&41 / &20) + s * (&41 / &20) \/
         ((&4 / &5) * c + (&3 / &5) * s) * (u + a) +
         ((&3 / &5) * c - (&4 / &5) * s) * (v + a) <= &287 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u + a <= c * (&41 / &20) + s * (&41 / &20)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CCC7SP_AVOID_AT) THEN
  SUBGOAL_THEN `u + a <= c * (&47 / &20) + s * (&33 / &20)` ASSUME_TAC THENL
   [CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&47 / &20) (&33 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s * (&41 / &20) + c * (&41 / &20)` ASSUME_TAC THENL
   [CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&41 / &20) (&41 / &20)`; ALL_TAC] THEN
  MP_TAC(SPECL [`--(u + a)`; `--u`; `--(v + a)`; `--v`;
                `--(c * (&47 / &20) + s * (&33 / &20))`;
                `--(--s * (&47 / &20) + c * (&33 / &20))`;
                `--(c * (&41 / &20) + s * (&41 / &20))`;
                `--(--s * (&41 / &20) + c * (&41 / &20))`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY CCC7SP_LIN THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1 - t` o REWRITE_RULE[ccc7sp_avoid] o
      check (fun th -> can (term_match [] `ccc7sp_avoid c s u v a`) (concl th))) THEN
    ANTS_TAC THENL [CCC7SP_LIN; ALL_TAC] THEN ANTS_TAC THENL [CCC7SP_LIN; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
    REWRITE_TAC[linside] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN CCC7SP_LIN;
    DISCH_TAC THEN CCC7SP_LIN]);;

(* Lean: positive (private) *)
let CCC7SP_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&3 / &2) (&2) /\ linside c s u v a (&2) (&3 / &2) /\
     ~linside c s u v a (&1) (&33 / &20) /\ ~linside c s u v a (&33 / &20) (&1) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ccc7sp_avoid c s u v a
     ==> linside c s u v a (&13 / &10) (&193 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCC7SP_POSITIVE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CCC7SP_AVOID_AT) THEN
  CCC7SP_UNFOLD_ALL_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&3 / &4`; `&3 / &25`] WFP_SHORT_PROJECTIONS)) THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `--(&7 / &20)`; `&93 / &100`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[linside] THEN
  MATCH_MP_TAC(TAUT `a /\ (b /\ c /\ d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL [ALL_TAC; REPEAT CONJ_TAC THEN CCC7SP_LIN] THEN
  ASM_CASES_TAC `c <= &11 * s` THENL
   [SUBGOAL_THEN `u + a <= c * (&41 / &20) + s * (&41 / &20)` ASSUME_TAC THENL
     [CCC7SP_CONTRA THEN CCC7SP_MISS `~linside c s u v a (&41 / &20) (&41 / &20)`; ALL_TAC] THEN
    CCC7SP_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCC7SP_UPPER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CCC7SP_LIN; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL [CCC7SP_LIN; ALL_TAC] THEN
  CCC7SP_CONTRA THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCC7SS_SHALLOW_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN CCC7SP_LIN; DISCH_TAC] THEN
  CCC7SP_PROD `&0 < ((&4 / &5) * c + (&3 / &5) * s) *
                    (u + a - (c * (&13 / &10) + s * (&193 / &100) + &1))` THEN
  CCC7SP_PROD `&0 < ((&3 / &5) * c - (&4 / &5) * s) *
                    (v + a - (--s * (&3 / &2) + c * &2))` THEN
  CCC7SP_LIN);;

(* the frame turn^3 o pullSwap, as a 5-tuple *)
let CCC7SP_SWAP = prove
 (`forall c t u v a x y. linside c t v u a x y <=> linside c (--t) u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: negative (private) *)
let CCC7SP_NEGATIVE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ s = --t /\
     &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&3 / &2) (&2) /\ linside c s u v a (&2) (&3 / &2) /\
     ~linside c s u v a (&1) (&33 / &20) /\ ~linside c s u v a (&33 / &20) (&1) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ccc7sp_avoid c s u v a
     ==> linside c s u v a (&13 / &10) (&193 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  MP_TAC(ONCE_REWRITE_RULE[CCC7SP_SWAP]
    (SPECL [`c:real`; `t:real`; `v:real`; `u:real`; `a:real`] CCC7SP_POSITIVE_FACES)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CCC7SP_AVOID_AT) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN CCC7SP_ANTS; STRIP_TAC] THEN
  CCC7SP_UNFOLD_ALL_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `--t:real`; `&7 / &10`; `&13 / &20`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--t:real`; `u:real`; `v:real`; `a:real`] CCC7SP_UPPER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CCC7SP_LIN; DISCH_TAC] THEN
  CCC7SP_PROD `&0 <= c * t` THEN
  SUBGOAL_THEN `u < c * (&13 / &10) + --t * (&193 / &100)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL [CCC7SP_LIN; ALL_TAC] THEN
    CCC7SP_CONTRA THEN
    MP_TAC(SPECL [`c:real`; `t:real`] CCC7SS_NEGATIVE_MARGIN) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN CCC7SP_ANTS; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    CCC7SP_PROD `&0 < ((&4 / &5) * c - (&3 / &5) * t) *
                      (u + a - (c * (&13 / &10) - t * (&193 / &100) + &1))` THEN
    CCC7SP_PROD `&0 < ((&3 / &5) * c + (&4 / &5) * t) * (v + a - (t * (&33 / &20) + c + &1))` THEN
    CCC7SP_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `v < t * (&13 / &10) + c * (&193 / &100)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [CCC7SP_FACT `&11 * t < c` THEN CCC7SP_LIN; ALL_TAC] THEN
    CCC7SP_CONTRA THEN
    CCC7SP_PROD `&0 <= t * t` THEN
    CCC7SP_FACT `&0 < (&7 / &5) * c + (&1 / &5) * t + (&9 / &125) * t * t +
                     (&101 / &250) * c * t - &114 / &125` THEN
    CCC7SP_PROD `&0 < ((&4 / &5) * c - (&3 / &5) * t) * (u + a - (c - t * (&33 / &20) + &1))` THEN
    CCC7SP_PROD `&0 < ((&3 / &5) * c + (&4 / &5) * t) *
                      (v + a - (t * (&13 / &10) + c * (&193 / &100) + &1))` THEN
    CCC7SP_LIN;
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN CCC7SP_LIN);;

(* Lean: point *)
let CCC7SP_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&3 / &2) (&2) /\ linside c s u v a (&2) (&3 / &2) /\
     ~linside c s u v a (&1) (&33 / &20) /\ ~linside c s u v a (&33 / &20) (&1) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&47 / &20) (&33 / &20) /\
     (forall w. &0 <= w ==> w <= &1 ==>
          ~linside c s u v a ((&1 - w) * (&41 / &20) + w * (&47 / &20))
                             ((&1 - w) * (&41 / &20) + w * (&33 / &20)))
     ==> linside c s u v a (&13 / &10) (&193 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  SUBGOAL_THEN `ccc7sp_avoid c' s' u' v' a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ccc7sp_avoid]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [MATCH_MP_TAC CCC7SP_POSITIVE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CCC7SP_NEGATIVE THEN EXISTS_TAC `--s':real` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
    UNDISCH_TAC `abs s' <= c'` THEN ASM_REAL_ARITH_TAC]);;
