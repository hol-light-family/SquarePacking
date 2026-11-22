(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryMarkerHalfpoint/            *)
(* Canonical.lean (N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint).*)
(* The actual forced faces for every offset and both canonical signs.        *)
(* Input is ocomhi_input; short_projections is WFP_SHORT_PROJECTIONS;      *)
(* CanonicalScalars.bounds is CCCS_BOUNDS.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryMarkerHalfpoint_Inputs.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCOMHC_LIN = NLIN_TAC ~deg2:false [];;

let OCOMHC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   OCOMHC_LIN; ALL_TAC];;

let OCOMHC_ANTS = REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC ORELSE OCOMHC_LIN);;

let OCOMHC_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [OCOMHC_LIN; ALL_TAC];;

let OCOMHC_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* contradiction with an omitted point: the point is inside after all *)
let OCOMHC_MISS_TAC t =
  UNDISCH_TAC t THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> false`) THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN OCOMHC_LIN;;

let OCOMHC_SETUP_TAC =
  FIRST_X_ASSUM(fun th -> if can (term_match [] `ocomhi_input c s u v a d`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[ocomhi_input] th) else NO_TAC) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> can (term_match [] `linside c s u v a x y`) (concl th)) ths));;

(* Lean: positive *)
let OCOMHC_POSITIVE = prove
 (`forall c s u v a d.
     c * c + s * s = &1 /\ &0 < a /\ ocomhi_input c s u v a d /\
     &0 < c /\ &0 <= s /\ s <= c
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCOMHC_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  OCOMHC_PROD `&0 <= d * c` THEN OCOMHC_PROD `&0 <= d * s` THEN
  OCOMHC_PROD `&0 <= c * (&13 / &50 - d)` THEN OCOMHC_PROD `&0 <= s * (&13 / &50 - d)` THEN
  SUBGOAL_THEN `--s - c <= v` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c s u v a (&1) (--(&1))`; ALL_TAC] THEN
  OCOMHC_FACT `u < (&1 + d) * c` THEN
  OCOMHC_FACT `v < --(&1 + d) * s` THEN
  OCOMHC_FACT `--(&1 + d) * s < v + a` THEN
  SUBGOAL_THEN `u + a <= (&1 + d) * c` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c s u v a (&1 + d) (&0)`; ALL_TAC] THEN
  OCOMHC_FACT `u < (&13 / &50) * c` THEN
  SUBGOAL_THEN `v + a <= --(&13 / &50) * s` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c s u v a (&13 / &50) (&0)`; ALL_TAC] THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&37 / &50`; `--(&1 / &2)`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN OCOMHC_LIN);;

(* Lean: negative_bands (private) *)
let OCOMHC_NEGATIVE_BANDS = prove
 (`forall c s u v a t x y. s = --t
     ==> (linside c s u v a x y <=>
          u < c * x - t * y /\ c * x - t * y < u + a /\
          v < t * x + c * y /\ t * x + c * y < v + a)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[linside] THEN
  REWRITE_TAC[REAL_ARITH `c * x + --t * y = c * x - t * y`;
              REAL_ARITH `-- --t * x + c * y = t * x + c * y`]);;

let OCOMHC_NEG_SETUP_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  OCOMHC_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN OCOMHC_ANTS; STRIP_TAC];;

(* Lean: negative_lower_impossible *)
let OCOMHC_NEGATIVE_LOWER_IMPOSSIBLE = prove
 (`forall c s u v a d t.
     c * c + s * s = &1 /\ &0 < a /\ ocomhi_input c s u v a d /\
     s = --t /\ &0 < c /\ &0 <= t /\ t <= c /\ t - c / &2 <= v
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCOMHC_NEG_SETUP_TAC THEN
  OCOMHC_PROD `&0 <= d * c` THEN OCOMHC_PROD `&0 <= d * t` THEN
  OCOMHC_PROD `&0 <= c * (&13 / &50 - d)` THEN
  SUBGOAL_THEN `(&13 / &50) * c <= u` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c (--t) u v a (&13 / &50) (&0)`; ALL_TAC] THEN
  OCOMHC_FACT `u < (&1 + d) * c` THEN
  OCOMHC_FACT `v < (&1 + d) * t` THEN
  OCOMHC_PROD `&0 <= (&13 / &50 - d) * (&13 / &50 + d)` THEN
  MP_TAC(SPECL [`c:real`; `--t:real`; `d:real`; `&1 / &2`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN OCOMHC_ANTS; STRIP_TAC] THEN
  OCOMHC_FACT `(&1 + d) * t < v + a` THEN
  SUBGOAL_THEN `u + a <= (&1 + d) * c` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c (--t) u v a (&1 + d) (&0)`; ALL_TAC] THEN
  OCOMHC_LIN);;

(* Lean: negative_upper_impossible *)
let OCOMHC_NEGATIVE_UPPER_IMPOSSIBLE = prove
 (`forall c s u v a d t.
     c * c + s * s = &1 /\ &0 < a /\ ocomhi_input c s u v a d /\
     s = --t /\ &0 < c /\ &0 <= t /\ t <= c /\ u + a <= c + t / &2
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCOMHC_NEG_SETUP_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `--t:real`; `&37 / &50`; `--(&1 / &2)`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OCOMHC_FACT `u < (&13 / &50) * c` THEN
  SUBGOAL_THEN `v + a <= (&13 / &50) * t` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c (--t) u v a (&13 / &50) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c + t` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c (--t) u v a (&1) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&13 / &50) * c + t` ASSUME_TAC THENL
   [OCOMHC_CONTRA THEN OCOMHC_MISS_TAC `~linside c (--t) u v a (&13 / &50) (--(&1))`; ALL_TAC] THEN
  OCOMHC_LIN);;

(* Lean: negative *)
let OCOMHC_NEGATIVE = prove
 (`forall c s u v a d t.
     c * c + s * s = &1 /\ &0 < a /\ ocomhi_input c s u v a d /\
     s = --t /\ &0 < c /\ &0 <= t /\ t <= c
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t - c / &2 <= v` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC OCOMHC_NEGATIVE_LOWER_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `d:real`; `t:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u + a <= c + t / &2` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC OCOMHC_NEGATIVE_UPPER_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `d:real`; `t:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  OCOMHC_NEG_SETUP_TAC THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN OCOMHC_LIN);;
