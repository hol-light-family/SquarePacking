(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/SingletonMissing.lean              *)
(* (N12Compact.CommonCases.SingletonMissing).  The stronger missing-corner   *)
(* singleton seeds (91/50,1) and (49/25,19/25).                              *)
(*                                                                           *)
(* Translation (as in CP_CommonCases_SingletonMissingFan.ml): Marker = Fin   *)
(* 16 is i < 16 with the Phase-1 table `marker`; Owns q i is                 *)
(* linside c s u v a (marker i$1) (marker i$2); ExactMarkers q {k} is        *)
(* !i. i < 16 ==> (Owns q i <=> i = k); pullSwap is LINSIDE_PULLSW.          *)
(* S12.singleton_forcing_template is unfolded into its case analysis; its    *)
(* ingredients are the Phase-1 lemmas of n12/phase1/auxcover.ml                *)
(* (corner_owner_center = CORNER_OWNER_CENTER, corner_nonavoidance_horizontal *)
(* = CORNER_H, bottom_segment_hit = BOTTOM_SEGMENT, general_segment_hit /    *)
(* descending = GEN_SEGMENT_HIT / GEN_SEGMENT_DESC, normal_bound_small =     *)
(* NB_SMALL) and side_region_hit (n12/phase1/singleton.ml, re-proved here).    *)
(* They are stated for the centred squares osq; CCSM_OWALLS supplies their   *)
(* wall hypothesis from lcont.  The wall cubic bound wall096_nonnegative is  *)
(* replaced by the Bernstein certificate CCSM_NB096 (ARC_NONNEG).            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "shared/tools/bernstein.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/SectionCapacity.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissingFan.ml";;

(* ------------------------------------------------------------------------- *)
(* Container walls: every closed support value of a contained square obeys  *)
(* the container bound (used for owalls).                                    *)
(* ------------------------------------------------------------------------- *)

let CCSM_SUPPORT_POINT = prove
 (`forall c s u v a nx ny K U V.
     c * c + s * s = &1 /\ &0 < a /\
     (forall x y. linside c s u v a x y ==> K <= nx * x + ny * y) /\
     (U = u \/ U = u + a) /\ (V = v \/ V = v + a)
     ==> K <= (nx * c + ny * s) * U + (--nx * s + ny * c) * V`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC
   [`&1`; `(nx * c + ny * s) * (u + a / &2 - U) + (--nx * s + ny * c) * (v + a / &2 - V)`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c * ((&1 - t) * U + t * (u + a / &2)) - s * ((&1 - t) * V + t * (v + a / &2))`;
    `s * ((&1 - t) * U + t * (u + a / &2)) + c * ((&1 - t) * V + t * (v + a / &2))`] o
    check (is_forall o concl)) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[linside] THEN
   SUBGOAL_THEN `forall P Q. c * (c * P - s * Q) + s * (s * P + c * Q) = P /\
                       --s * (c * P - s * Q) + c * (s * P + c * Q) = Q`
     (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPECL [`t:real`; `a:real`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   MP_TAC(SPECL [`&1 - t`; `a:real`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl))) THEN
   REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `X = Y + d * t ==> K <= X ==> &0 <= Y - K + d * t`) THEN
  CONV_TAC REAL_RING);;

let CCSM_SUPPORT_LOWER = prove
 (`forall c s u v a nx ny K.
     c * c + s * s = &1 /\ &0 < a /\
     (forall x y. linside c s u v a x y ==> K <= nx * x + ny * y)
     ==> K <= ABT_lower c s u v a nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ABT_lower c s u v a nx ny =
    (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) -
    a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))` SUBST1_TAC THENL
  [REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `nx:real`; `ny:real`;
                `K:real`] CCSM_SUPPORT_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = nx * c + ny * s` THEN ABBREV_TAC `h = --nx * s + ny * c` THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (p,q) -> FIRST_ASSUM(MP_TAC o SPECL [p; q]) THEN REWRITE_TAC[] THEN
                          DISCH_TAC)
   [`u:real`,`v:real`; `u:real`,`v + a:real`; `u + a:real`,`v:real`;
    `u + a:real`,`v + a:real`] THEN
  ASM_CASES_TAC `&0 <= k` THEN ASM_CASES_TAC `&0 <= h` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`;
               REAL_ARITH `~(&0 <= x) ==> abs x = --x`] THEN
  RASM_ARITH_TAC);;

let CCSM_LOWER_AXES = prove
 (`forall c s u v a.
     ABT_lower c s u v a (&1) (&0) = lcx c s u v a - (abs c + abs s) * a / &2 /\
     ABT_lower c s u v a (--(&1)) (&0) = --lcx c s u v a - (abs c + abs s) * a / &2 /\
     ABT_lower c s u v a (&0) (&1) = lcy c s u v a - (abs c + abs s) * a / &2 /\
     ABT_lower c s u v a (&0) (--(&1)) = --lcy c s u v a - (abs c + abs s) * a / &2`,
  REWRITE_TAC[ABT_lower; tss_support_radius] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_LNEG;
              REAL_NEG_NEG; REAL_NEG_0; REAL_SUB_RZERO; REAL_ABS_NEG] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

let CCSM_OWALLS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ lcont c s u v a
     ==> owalls (lcx c s u v a) (lcy c s u v a) c s a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (nx,ny,k) ->
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; nx; ny; k]
      CCSM_SUPPORT_LOWER) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
     FIRST_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o REWRITE_RULE[lcont] o
       check (fun th -> can (term_match [] `lcont c s u v a`) (concl th))) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     REWRITE_TAC[CCSM_LOWER_AXES]])
   [`&1`,`&0`,`&0`; `--(&1)`,`&0`,`--(&4)`; `&0`,`&1`,`&0`; `&0`,`--(&1)`,`--(&4)`] THEN
  REWRITE_TAC[owalls] THEN
  SPEC_TAC(`(abs c + abs s) * a / &2`,`r:real`) THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase-1 side_region_hit (n12/phase1/singleton.ml), re-proved locally.       *)
(* ------------------------------------------------------------------------- *)

let CCSM_BOTTOM_ROW = prove
 (`forall c1 c2 a b l x0 bb.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        x0 <= c1 /\ c1 <= x0 + &1 /\ c2 <= bb /\ bb <= &457 / &500
        ==> vector[x0; bb] IN osq c1 c2 a b l \/ vector[x0 + &1; bb] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MP_TAC(SPECL [`c1 - x0`; `c2:real`; `c:real`; `s:real`; `l:real`; `bb:real`]
         WALL_ROW_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_OSQ] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN BINOP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let CCSM_SIDE_REGION_HIT = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        c1 <= &457 / &500 /\ &1 <= c2 /\ c2 <= &2
        ==> vector[&457 / &500; &1] IN osq c1 c2 a b l \/
            vector[&457 / &500; &2] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SW_RULE (SPECL [`c2:real`; `c1:real`; `b:real`; `a:real`; `l:real`; `&1`;
                         `&457 / &500`] CCSM_BOTTOM_ROW)) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `a * a + b * b = &1` THEN
                  RASM_ARITH_TAC; REWRITE_TAC[]]);;

(* Lean: wall096_nonnegative (private); the wall bound it yields *)
let CCSM_NB096 =
  ARC_NONNEG `c + s - (c * c * (&19 / &25) + s * s + (&24 / &25) * c * s)`;;

(* ------------------------------------------------------------------------- *)
(* The seeds.                                                                *)
(* ------------------------------------------------------------------------- *)

let CCSM_NBS_TAC =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NB_SMALL THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV;;

let CCSM_NB096_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CCSM_NB096) THEN
  REAL_ARITH_TAC;;

(* apply a Phase-1 lemma at the centre of the square; the conclusion is
   translated back to linside *)
let CCSM_P1 th args ntac =
  MP_TAC(SPECL ([`lcx c s u v a`; `lcy c s u v a`; `c:real`; `s:real`; `a:real`] @ args) th) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   FIRST [FIRST_ASSUM ACCEPT_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
          RASM_ARITH_TAC; ntac];
   ASM_SIMP_TAC[CCSMF_OSQ_CENTRE]];;

let CCSM_INTRO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSM_OWALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MARKER_EXPLICIT; VECTOR_2]) THEN
  MP_TAC(SPECL [`lcx c s u v a`; `lcy c s u v a`; `c:real`; `s:real`; `a:real`]
    CORNER_OWNER_CENTER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CCSMF_OSQ_CENTRE]; STRIP_TAC] THEN
  CCSMF_MARKERS_TAC THEN
  ASM_CASES_TAC `lcx c s u v a <= &457 / &500` THENL
  [ASM_CASES_TAC `lcy c s u v a <= &1` THENL
   [CCSM_P1 CORNER_H [`&457 / &500`] ALL_TAC;
    CCSM_P1 CCSM_SIDE_REGION_HIT [] ALL_TAC];
   ALL_TAC];;

let CCSM_REPL_TAC th =
  MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;;

(* Lean: point182 *)
let CCSM_POINT182 = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
     lcont c s u v a /\ linside c s u v a (marker 0$1) (marker 0$2) /\
     (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
     ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&91 / &50) (&1)`,
  CCSM_INTRO_TAC THEN
  ASM_CASES_TAC `lcx c s u v a <= &91 / &50` THENL
  [ASM_CASES_TAC `lcy c s u v a <= &1` THENL
   [ASM_CASES_TAC `lcx c s u v a <= &1` THENL
    [CCSM_P1 CORNER_H [`&1`] ALL_TAC;
     CCSM_P1 BOTTOM_SEGMENT [`&1`; `&91 / &50`; `&1`] ALL_TAC];
    CCSM_REPL_TAC CCSMF_REPLACEMENT182_LEFT];
   ASM_CASES_TAC `lcy c s u v a <= &1` THENL
   [CCSM_P1 GEN_SEGMENT_DESC [`&91 / &50`; `&2`; `&1`; `&457 / &500`] CCSM_NBS_TAC;
    CCSM_REPL_TAC CCSMF_REPLACEMENT182_RIGHT]]);;

(* Lean: point196 *)
let CCSM_POINT196 = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
     lcont c s u v a /\ linside c s u v a (marker 0$1) (marker 0$2) /\
     (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
     ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&49 / &25) (&19 / &25)`,
  CCSM_INTRO_TAC THEN
  ASM_CASES_TAC `lcx c s u v a <= &49 / &25` THENL
  [ASM_CASES_TAC `lcy c s u v a <= &1` THENL
   [ASM_CASES_TAC `lcx c s u v a <= &1` THENL
    [CCSM_P1 CORNER_H [`&1`] ALL_TAC;
     CCSM_P1 GEN_SEGMENT_DESC [`&1`; `&49 / &25`; `&1`; `&19 / &25`] CCSM_NB096_TAC];
    CCSM_REPL_TAC CCSMF_REPLACEMENT196_LEFT];
   ASM_CASES_TAC `lcy c s u v a <= &457 / &500` THENL
   [CCSM_P1 GEN_SEGMENT_HIT [`&49 / &25`; `&2`; `&19 / &25`; `&457 / &500`] CCSM_NBS_TAC;
    CCSM_REPL_TAC CCSMF_REPLACEMENT196_RIGHT]]);;

(* Lean: forces *)
let CCSM_FORCES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
     lcont c s u v a /\ linside c s u v a (marker 0$1) (marker 0$2) /\
     (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
     ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&91 / &50) (&1) /\
         linside c s u v a (&49 / &25) (&19 / &25)`,
  MESON_TAC[CCSM_POINT182; CCSM_POINT196]);;

(* Lean: zero_missing_points *)
let CCSM_ZERO_MISSING_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
     lcont c s u v a /\
     (forall i. i < 16 ==> (linside c s u v a (marker i$1) (marker i$2) <=> i = 0)) /\
     ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&91 / &50) (&1) /\
         linside c s u v a (&49 / &25) (&19 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCSM_FORCES THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ARITH];
   GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]]);;

(* Lean: one_missing_points *)
let CCSM_ONE_MISSING_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
     lcont c s u v a /\
     (forall i. i < 16 ==> (linside c s u v a (marker i$1) (marker i$2) <=> i = 1)) /\
     ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&1) (&91 / &50) /\
         linside c s u v a (&19 / &25) (&49 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`]
    CCSM_ZERO_MISSING_POINTS) THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[LCONT_PULLSW] THEN NO_TAC;
         UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM((fun th ->
    let facts = map (fun j ->
      CONV_RULE (NUM_REDUCE_CONV) (REWRITE_RULE[MARKER_EXPLICIT; VECTOR_2]
        (MP (SPEC (mk_small_numeral j) th)
            (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool`
               (mk_small_numeral j) `16`)))))) (0--15) in
    REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC facts) o
    check (fun th -> is_forall(concl th))));;
