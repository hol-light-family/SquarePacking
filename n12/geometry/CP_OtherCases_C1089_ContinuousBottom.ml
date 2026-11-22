(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1089/ContinuousBottom.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C1089.ContinuousBottom).     *)
(* Proposition 1 of C1089-CONTINUOUS-REDUCTION.  W is the tuple c s u v a;  *)
(* pullSwap W = (s, c, u, --v - a, a) (LINSIDE_PULLSW, LCONT_PULLSW);       *)
(* centerX W = lcx c s u v a.                                                *)
(* WallLowerCenterBarrier.center_above: WLCB_CENTER_ABOVE;                  *)
(* WallSignChord.chord: WSC_CHORD; C981CompletionWallAdvance.point:          *)
(* C981WA_POINT; OriginalOwners.horizontal_segment: OO_HORIZONTAL_SEGMENT.   *)
(* ========================================================================= *)

needs "n12/geometry/WallLowerCenterBarrier.ml";;
needs "n12/geometry/WallSignChord.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: center_pullSwap_y (S12) *)
let C1089CB_CENTER_PULLSW = prove
 (`forall c s u v a. lcy s c u (--v - a) a = lcx c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

let C1089CB_SWAP_TAC =
  REWRITE_TAC[LINSIDE_PULLSW] THEN ASM_SIMP_TAC[LCONT_PULLSW] THEN
  TRY(CONV_TAC REAL_RAT_REDUCE_CONV) THEN RASM_ARITH_TAC;;

(* the center cut on the swapped square *)
let C1089CB_HIGH = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&2) (&457 / &500) /\ linside c s u v a (&12 / &5) (&1) /\
     ~linside c s u v a (&87 / &50) (&1) /\ ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> &21 / &10 < lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM C1089CB_CENTER_PULLSW] THEN
  MATCH_MP_TAC WLCB_CENTER_ABOVE THEN ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
  ASM_SIMP_TAC[LCONT_PULLSW] THEN RASM_ARITH_TAC);;

(* Lean: near_of_far *)
let C1089CB_NEAR_OF_FAR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&12 / &5) (&1) /\
     ~linside c s u v a (&87 / &50) (&1) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> &21 / &10 < lcx c s u v a /\ linside c s u v a (&113 / &50) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&21 / &10 < lcx c s u v a` ASSUME_TAC THENL
   [MATCH_MP_TAC C1089CB_HIGH THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN MATCH_MP_TAC WSC_CHORD THEN
  ASM_REWRITE_TAC[LINSIDE_PULLSW; C1089CB_CENTER_PULLSW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [RASM_ARITH_TAC;
    UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN MESON_TAC[];
    RASM_ARITH_TAC]);;

(* Lean: reach *)
let C1089CB_REACH = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&12 / &5) (&1) /\
     linside c s u v a (&113 / &50) (&1) /\
     ~linside c s u v a (&87 / &50) (&1) /\
     ~linside c s u v a (&187 / &100) (&19 / &25) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> &51 / &25 < lcx c s u v a /\ linside c s u v a (&14 / &5) (&1) /\
         forall x. &113 / &50 <= x /\ x <= &14 / &5 ==> linside c s u v a x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&21 / &10 < lcx c s u v a` ASSUME_TAC THENL
   [MATCH_MP_TAC C1089CB_HIGH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside c s u v a (&14 / &5) (&1)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN MATCH_MP_TAC C981WA_POINT THEN
    ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN ASM_SIMP_TAC[LCONT_PULLSW] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: reach_of_far *)
let C1089CB_REACH_OF_FAR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&12 / &5) (&1) /\
     ~linside c s u v a (&87 / &50) (&1) /\
     ~linside c s u v a (&187 / &100) (&19 / &25) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> &51 / &25 < lcx c s u v a /\ linside c s u v a (&14 / &5) (&1) /\
         forall x. &113 / &50 <= x /\ x <= &14 / &5 ==> linside c s u v a x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1089CB_REACH THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL C1089CB_NEAR_OF_FAR) THEN ASM_SIMP_TAC[]);;

(* Lean: family *)
let c1089cb_family = new_definition
 `c1089cb_family = {1,12,48,192,256,512,1024,2048,4096,8192,16384,32768}`;;

(* Lean: bottomComponents *)
let c1089cb_bottom_components = new_definition
 `c1089cb_bottom_components = [{6,15}; {6,15,18}; {4,6,15}]:(num->bool)list`;;

(* Lean: original_bottom *)
let C1089CB_ORIGINAL_BOTTOM =
  let c1089cb_f = `c1089cb_family` in
  let c1089cb_marker = oo_inst c1089cb_f (oo_seed 8192 (`&2`, `&457 / &500`))
  and c1089cb_singleton = oo_inst c1089cb_f (oo_seed 1 (`&87 / &50`, `&1`))
  and c1089cb_seed = oo_inst c1089cb_f (oo_seed 1 (`&187 / &100`, `&19 / &25`))
  and c1089cb_central = oo_inst c1089cb_f (oo_seed 512 (`&47 / &20`, `&33 / &20`))
  and c1089cb_apart0 = oo_apart c1089cb_f 8192 1 and c1089cb_apart5 = oo_apart c1089cb_f 8192 512 in
  prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1089cb_family /\
     MEM (ooaux c1 c2 a b l 8192) c1089cb_bottom_components
     ==> &51 / &25 < lcx (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                          (oov c1 c2 a b l 8192) l /\
         linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                 (oov c1 c2 a b l 8192) l (&14 / &5) (&1) /\
         forall x. &113 / &50 <= x /\ x <= &14 / &5
             ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                         (oov c1 c2 a b l 8192) l x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192` MP_TAC THENL
   [UNDISCH_TAC `MEM (ooaux c1 c2 a b l 8192) c1089cb_bottom_components` THEN
    REWRITE_TAC[c1089cb_bottom_components; MEM] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM (oo_aux_point 6); GSYM (oo_aux_point 15)] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL c1089cb_marker) THEN MP_TAC(SPEC_ALL c1089cb_singleton) THEN MP_TAC(SPEC_ALL c1089cb_seed) THEN
  MP_TAC(SPEC_ALL c1089cb_central) THEN MP_TAC(SPEC_ALL c1089cb_apart0) THEN MP_TAC(SPEC_ALL c1089cb_apart5) THEN
  ASM_REWRITE_TAC[ldisj] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC C1089CB_REACH THEN ASM_SIMP_TAC[OO_UNIT; OO_SIDE; OO_BOX] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[]);;
