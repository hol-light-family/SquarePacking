(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ElbowProfile.lean                         *)
(* (N12Compact.C1092ElbowProfile).  The residual-elbow profile from strict   *)
(* anchors and five weak exclusions.  Normal: c977cc_normal;                 *)
(* OtherCases.ElbowPoint: OCEP_*; ClosedFrames.canonical_frame:              *)
(* CLF_CANONICAL_FRAME; short_projections: WFP_SP.                           *)
(* mirror (c,s,u,v,a) is the 5-tuple (c, --s, --u - a, v, a):                *)
(*   (mirror C).Inside x y <=> C.Inside (-x) y.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

let C1092EP_LIN (asl,w as g) =
  if is_eq w then (REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
                   NLIN_TAC ~deg2:false []) g
  else NLIN_TAC ~deg2:false [] g;;

let C1092EP_PROD a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092EP_LIN; DISCH_TAC];;
let C1092EP_PRODLT a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092EP_LIN; DISCH_TAC];;

(* Lean: inside_mirror (private) *)
let C1092EP_INSIDE_MIRROR = prove
 (`forall c s u v a x y. linside c (--s) (--u - a) v a x y <=> linside c s u v a (--x) y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: Profile (structure) *)
let c1092ep_profile = new_definition
 `c1092ep_profile c s u v a <=>
    c977cc_normal c s /\ &0 < s /\
    --c - (&2 / &5) * s <= u /\ u + a <= --(&13 / &50) * s /\
    (&2 / &5) * s - c <= v /\ v + a <= (&7 / &20) * (c + s) /\
    linside c s u v a (&0) (--(&1 / &2)) /\
    s / (&1 + c) < &7 / &50 /\ &24 / &25 < c /\ s < &7 / &25 /\ c + s < &31 / &25`;;

let C1092EP_USE th =
  MP_TAC(SPECL [`c:real`; `--s`; `--u - a`; `v:real`; `a:real`] th) THEN
  REWRITE_TAC[C1092EP_INSIDE_MIRROR; REAL_NEG_NEG; REAL_NEG_0];;

(* Lean: canonical_profile *)
let C1092EP_CANONICAL_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     linside c s u v a (--(&1)) (--(&13 / &50)) /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (--(&1)) (--(&2 / &5)) /\
     ~linside c s u v a (--(&543 / &500)) (&0) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a (--(&2 / &5)) (--(&1))
     ==> c1092ep_profile c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_ABS_BOUNDS] o
    check (fun th -> concl th = `abs s <= c`)) THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN C1092EP_USE OCEP_POSITIVE_IMPOSSIBLE THEN
   REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   (FIRST_ASSUM ACCEPT_TAC ORELSE C1092EP_LIN); ALL_TAC] THEN
  C1092EP_USE OCEP_NEGATIVE_FACES THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE C1092EP_LIN);
                  STRIP_TAC] THEN
  C1092EP_USE OCEP_POINTS THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE C1092EP_LIN);
                  STRIP_TAC] THEN
  SUBGOAL_THEN `c977cc_normal c s` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN C1092EP_LIN; ALL_TAC] THEN
  PCT_NORMAL_TAC THEN
  MP_TAC(WFP_SP `&61 / &100` `&7 / &20`) THEN MP_TAC(WFP_SP `&2 / &5` `&37 / &50`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_neg(concl th)) &&
     can (find_term ((=) `linside`)) (concl th)))) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v < --(&13 / &50) * c` ASSUME_TAC THENL [C1092EP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= --(&13 / &50) * s` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&0) (--(&13 / &50))` THEN
   REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN C1092EP_LIN;
   ALL_TAC] THEN
  SUBGOAL_THEN `u < --(&2 / &5) * c - s` ASSUME_TAC THENL [C1092EP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * s - c <= v` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (--(&2 / &5)) (--(&1))` THEN
   REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN C1092EP_LIN;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + (&7 / &50) * s` ASSUME_TAC THENL [C1092EP_LIN; ALL_TAC] THEN
  ABBREV_TAC `z = s / (&1 + c)` THEN
  SUBGOAL_THEN `z * (&1 + c) = s /\ s * z = &1 - c` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "z" THEN UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL
  [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN C1092EP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `z < &7 / &50` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092EP_PROD `s:real` `z - &7 / &50` THEN C1092EP_LIN; ALL_TAC] THEN
  C1092EP_PROD `z:real` `&1 - c` THEN
  SUBGOAL_THEN `s < &7 / &25` ASSUME_TAC THENL [C1092EP_LIN; ALL_TAC] THEN
  C1092EP_PRODLT `s:real` `&7 / &50 - z` THEN
  SUBGOAL_THEN `&24 / &25 < c` ASSUME_TAC THENL [C1092EP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * s = &2 * z`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092EP_PROD `&7 / &50 - z` `&2 - (&56 / &25) * (&7 / &50 + z)` THEN
  SUBGOAL_THEN `&0 < &6 / &25 - &2 * z + (&56 / &25) * z pow 2` ASSUME_TAC THENL
  [C1092EP_LIN; ALL_TAC] THEN
  MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c + s < &31 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092EP_PROD `&1 + z pow 2` `(c + s) - &31 / &25` THEN C1092EP_LIN; ALL_TAC] THEN
  REWRITE_TAC[c1092ep_profile; linside] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092EP_LIN);;

(* Lean: exists_profile *)
let C1092EP_EXISTS_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     linside c s u v a (--(&1)) (--(&13 / &50)) /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (--(&1)) (--(&2 / &5)) /\
     ~linside c s u v a (--(&543 / &500)) (&0) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a (--(&2 / &5)) (--(&1))
     ==> exists c' s' u' v' a'. a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           c1092ep_profile c' s' u' v' a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092EP_CANONICAL_PROFILE THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092EP_LIN);;
