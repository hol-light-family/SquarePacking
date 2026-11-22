(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryMarkerHalfpoint/Main.lean   *)
(* (N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint).               *)
(* ORDINARY-MARKER-HALFPOINT Theorem 1 and its two applications.  Input is   *)
(* ocomhi_input; q.translated 2 2 is (c, s, u - 2c - 2s, v + 2s - 2c, a);    *)
(* pullY is LINSIDE_PULLY; pullY o pullX is OCOMHM_PULLXY.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryMarkerHalfpoint_Canonical.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* S12.inside_translated_iff at (2,2) *)
let OCOMHM_TRANSLATED = prove
 (`forall c s u v a x y.
     linside c s (u - &2 * c - &2 * s) (v + &2 * s - &2 * c) a x y <=>
     linside c s u v a (&2 + x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let OCOMHM_PULLXY = prove
 (`forall c s u v a x y.
     linside (--c) (--s) (u - &4 * c - &4 * s) (v + &4 * s - &4 * c) a x y <=>
     linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point *)
let OCOMHM_POINT = prove
 (`forall c s u v a d. c * c + s * s = &1 /\ &0 < a /\ ocomhi_input c s u v a d
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `d:real`]
    OCOMHI_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th))) &&
      can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [MATCH_MP_TAC OCOMHC_POSITIVE THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCOMHC_NEGATIVE THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `--s':real`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: point_original *)
let OCOMHM_POINT_ORIGINAL = prove
 (`forall c s u v a d.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 <= d /\ d <= &13 / &50 /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\ linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3 + d) (&2) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&113 / &50) (&1)
     ==> linside c s u v a (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - &2 * c - &2 * s`; `v + &2 * s - &2 * c`;
                `a:real`; `d:real`] OCOMHM_POINT) THEN
  REWRITE_TAC[ocomhi_input; OCOMHM_TRANSLATED;
              REAL_ARITH `&2 + (&1 + d) = &3 + d`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* Lean: northeast_halfpoint *)
let OCOMHM_NORTHEAST_HALFPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&113 / &50) /\ linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&113 / &50) (&3)
     ==> linside c s u v a (&3) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`; `&43 / &500`]
    OCOMHM_POINT_ORIGINAL) THEN
  REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

(* Lean: northwest_halfpoint *)
let OCOMHM_NORTHWEST_HALFPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&1) (&113 / &50) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&457 / &500) (&2) /\
     ~linside c s u v a (&1) (&3) /\
     ~linside c s u v a (&87 / &50) (&3)
     ==> linside c s u v a (&1) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--c:real`; `--s:real`; `u - &4 * c - &4 * s`; `v + &4 * s - &4 * c`;
                `a:real`; `&43 / &500`] OCOMHM_POINT_ORIGINAL) THEN
  REWRITE_TAC[OCOMHM_PULLXY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;
