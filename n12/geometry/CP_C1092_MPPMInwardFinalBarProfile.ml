(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalBarProfile.lean           *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  NEGATIVE-SUCCESSOR-BAR-     *)
(* PROFILE with the actual whole right bar.  Square E is c s u v a, the bar  *)
(* owner R is cR sR uR vR aR.  Normal: c977cc_normal; half / quarter_data:   *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA; WallProfile.vertex /               *)
(* strict_closed_segment: OCWPVG_VERTEX / OCWPVG_STRICT_CLOSED_SEGMENT;      *)
(* NegativeSuccessor: c1092ifsu_negsucc.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* expand the positive linside assumptions into their four components *)
let C1092IFBP_OPEN_TAC =
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (can (term_match [] `linside c s u v a x y`) o concl)));;

(* a weak face bound p <= q from an omitted point: assume q < p, show the point *)
let C1092IFBP_MISS_TAC tm =
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN UNDISCH_TAC tm THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: successor_preliminary *)
let C1092IFBP_SUCCESSOR_PRELIMINARY = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\ s < &0 /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (--(&1)) /\
     linside c s u v a (&2 / &5) (--(&1)) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&0) (--(&543 / &500))
     ==> --(&13 / &50) * s <= u /\ u + a <= c - s /\
         --(&543 / &500) * c <= v /\ v + a <= --s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN C1092IFBP_OPEN_TAC THEN
  SUBGOAL_THEN `--(&13 / &50) * s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v + a <= --(&13 / &50) * c` ASSUME_TAC THENL
     [C1092IFBP_MISS_TAC `~linside c s u v a (&0) (--(&13 / &50))`; ALL_TAC] THEN
    SUBGOAL_THEN `u + a <= c - s` ASSUME_TAC THENL
     [C1092IFBP_MISS_TAC `~linside c s u v a (&1) (--(&1))`; ALL_TAC] THEN
    SUBGOAL_THEN `--(&543 / &500) * s <= u` ASSUME_TAC THENL
     [C1092IFBP_MISS_TAC `~linside c s u v a (&0) (--(&543 / &500))`; ALL_TAC] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (&1) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c - s` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (&1) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * c <= v` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (&0) (--(&543 / &500))`; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: crossing_right (private) *)
let C1092IFBP_CROSSING_RIGHT = prove
 (`forall c s u v a cR sR uR vR aR X Y.
     lclosed c s u v a X Y /\ linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     &1 < X /\ --(&2 / &5) < Y /\ Y < &0 /\
     (forall y. --(&2 / &5) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     ldisj c s u v a cR sR uR vR aR ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  ABBREV_TAC `z = (X - &1) / (X - &7 / &20)` THEN
  SUBGOAL_THEN `&0 < X - &7 / &20` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z * (X - &7 / &20) = X - &1` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < z /\ z < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_ARITH
      `&1 < X ==> &0 < X - &1`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `X:real`; `Y:real`;
                `&7 / &20`; `--(&7 / &20)`; `z:real`] OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - z) * X + z * &7 / &20 = &1` SUBST1_TAC THENL
   [UNDISCH_TAC `z * (X - &7 / &20) = X - &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `(&1 - z) * Y + z * --(&7 / &20)`]) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  C1092PRS_PROD `&0 <= (&1 - z) * (Y + &2 / &5)` THEN
  C1092PRS_PROD `&0 <= (&1 - z) * --Y` THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* scalar steps of successor_bar_cap (local) *)
let C1092IFBP_SMALL = prove
 (`forall c s u a.
     c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\ --(&13 / &50) * s <= u /\
     u + a <= c - &2 / &5 * s ==> --s < &7 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&1 < c - &7 / &50 * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c (--s)`, `z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (c - &7 / &50 * s - &1) = &2 * z * (&7 / &50 - z)`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * c = &1 - z pow 2`;
                           `(&1 + z pow 2) * --s = &2 * z`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092PRS_PROD `&0 < (&1 + z pow 2) * (c - &7 / &50 * s - &1)` THEN
  SUBGOAL_THEN `z < &7 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092PRS_PROD `&0 <= (&2 * z) * (z - &7 / &50)` THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  C1092PRS_PROD `&0 <= --s * z pow 2` THEN NLIN_TAC ~deg2:false []);;

let C1092IFBP_UPPER_Y = prove
 (`forall c s u v a.
     c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\ --(&13 / &50) * s <= u /\
     v + a <= --s ==> s * (u + a) + c * (v + a) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= --s * (u - --(&13 / &50) * s)` THEN
  C1092PRS_PROD `&0 <= c * (--s - (v + a))` THEN
  C1092PRS_PROD `&0 < --s * (a - c)` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `s:real`]);;

let C1092IFBP_LOWER_Y = prove
 (`forall c s u v a.
     c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\ u + a <= c - &2 / &5 * s /\
     --(&543 / &500) * c <= v /\ --s < &7 / &25
     ==> --(&2 / &5) < s * (u + a) + c * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= --s * ((c - &2 / &5 * s) - (u + a))` THEN
  C1092PRS_PROD `&0 <= c * (v - --(&543 / &500) * c)` THEN
  C1092PRS_PROD `&0 < c * (a - &1)` THEN
  C1092PRS_PROD `&0 <= c * (&1 - c)` THEN
  C1092PRS_PROD `&0 <= --s * (&1 - c)` THEN
  C1092PRS_PROD `&0 <= (&7 / &25 + s) * (&7 / &25 - s)` THEN
  NLIN_TAC []);;

let C1092IFBP_RIGHT_X = prove
 (`forall c s u v a.
     c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\ --(&13 / &50) * s <= u /\
     --(&543 / &500) * c <= v /\ --s < &7 / &25
     ==> &1 < c * (u + a) - s * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= c * (u - --(&13 / &50) * s)` THEN
  C1092PRS_PROD `&0 <= --s * (v - --(&543 / &500) * c)` THEN
  C1092PRS_PROD `&0 < (a - &1) * (c - s)` THEN
  C1092PRS_PROD `&0 <= (&32 / &25 - (c - s)) * (c - s - &1)` THEN
  SUBGOAL_THEN `&1 - &50 / &57 * c * s <= c - s` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092PRS_PROD `&0 < c * --s` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: successor_bar_cap *)
let C1092IFBP_SUCCESSOR_BAR_CAP = prove
 (`forall c s u v a cR sR uR vR aR.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\ s < &0 /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (--(&1)) /\
     linside c s u v a (&2 / &5) (--(&1)) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&0) (--(&543 / &500)) /\
     (forall y. --(&2 / &5) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     ldisj c s u v a cR sR uR vR aR
     ==> v + a <= --s - &2 / &5 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFBP_SUCCESSOR_PRELIMINARY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~linside c s u v a (&1) (--(&2 / &5))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `ldisj c s u v a cR sR uR vR aR` THEN REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1`; `--(&2 / &5)`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `u + a <= c - &2 / &5 * s` THENL
   [ALL_TAC;
    C1092PRS_NORMAL_TAC THEN C1092IFBP_OPEN_TAC THEN
    C1092IFBP_MISS_TAC `~linside c s u v a (&1) (--(&2 / &5))`] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `a:real`] C1092IFBP_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `cR:real`; `sR:real`;
                `uR:real`; `vR:real`; `aR:real`; `c * (u + a) - s * (v + a)`;
                `s * (u + a) + c * (v + a)`] C1092IFBP_CROSSING_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C1092IFBP_UPPER_Y; C1092IFBP_LOWER_Y; C1092IFBP_RIGHT_X] THEN
  MATCH_MP_TAC OCWPVG_VERTEX THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: negative_successor *)
let C1092IFBP_NEGATIVE_SUCCESSOR = prove
 (`forall c s u v a cR sR uR vR aR.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\ s < &0 /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (--(&1)) /\
     linside c s u v a (&2 / &5) (--(&1)) /\
     linside c s u v a (&1 / &2) (--(&1)) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&0) (--(&543 / &500)) /\
     (forall y. --(&2 / &5) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     ldisj c s u v a cR sR uR vR aR
     ==> c1092ifsu_negsucc c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFBP_SUCCESSOR_PRELIMINARY) THEN
  MP_TAC(SPEC_ALL C1092IFBP_SUCCESSOR_BAR_CAP) THEN
  ASM_REWRITE_TAC[c1092ifsu_negsucc] THEN SIMP_TAC[]);;
