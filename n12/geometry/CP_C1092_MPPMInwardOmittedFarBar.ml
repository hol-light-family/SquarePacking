(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardOmittedFarBar.lean             *)
(* (namespace N12Compact.C1092MPPMInwardOmittedFar).  CENTERED-INWARD-       *)
(* OMITTED-G-FAR-ENDING section 1: the whole far right bar caps an actual    *)
(* negative successor.  E is c s u v a, the bar owner R is cR sR uR vR aR.   *)
(* Normal: c977cc_normal; half / quarter_data: C1092WPS_half /               *)
(* C1092WPS_QUARTER_DATA; NegativeSuccessor: c1092ifsu_negsucc; width_half:  *)
(* C1092IFSU_WIDTH_HALF; canonical_bounds: C1092PRS_CANONICAL_BOUNDS;        *)
(* WallProfile.vertex / strict_closed_segment: OCWPVG_*.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBarProfile.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;

(* Lean: narrow_support (private) *)
let C1092IOFB_NARROW_SUPPORT = prove
 (`forall d t. c977cc_normal d t /\ C1092WPS_half d t < &3 / &10
     ==> t + (&263 / &500) * d < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `C1092WPS_half d t < &3 / &10` THEN
  SPEC_TAC(`C1092WPS_half d t`, `z:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  ASSUME_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
  C1092PRS_PROD `&0 <= (&3 / &10 - z) * (&2 - (&763 / &500) * (z + &3 / &10))` THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (&1 - t - (&263 / &500) * d) =
                &237 / &500 + (&763 / &500) * z pow 2 - &2 * z` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * d = &1 - z pow 2`;
                           `(&1 + z pow 2) * t = &2 * z`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 <= (&1 + z pow 2) * ((t + (&263 / &500) * d) - &1)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: crossing_right (private) *)
let C1092IOFB_CROSSING_RIGHT = prove
 (`forall c s u v a cR sR uR vR aR X Y.
     lclosed c s u v a X Y /\ linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     &1 < X /\ --(&14 / &25) < Y /\ Y < &0 /\
     (forall y. --(&14 / &25) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
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
  C1092PRS_PROD `&0 <= (&1 - z) * (Y + &14 / &25)` THEN
  C1092PRS_PROD `&0 <= (&1 - z) * --Y` THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* the narrow half angle of the exfalso branch (local) *)
let C1092IOFB_NARROW = prove
 (`forall c s u a.
     c977cc_normal c (--s) /\ &1 < a /\ --(&13 / &50) * s <= u /\
     u + a <= c - (&14 / &25) * s ==> C1092WPS_half c (--s) < &3 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&1 < c - (&3 / &10) * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c (--s)`, `z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (c - &3 / &10 * s - &1) = &2 * z * (&3 / &10 - z)`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * c = &1 - z pow 2`;
                           `(&1 + z pow 2) * --s = &2 * z`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092PRS_PROD `&0 < (&1 + z pow 2) * (c - &3 / &10 * s - &1)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 <= (&2 * z) * (z - &3 / &10)` THEN NLIN_TAC ~deg2:false []);;

let C1092IOFB_UPPER_Y = prove
 (`forall c s u v a.
     c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\ --(&13 / &50) * s <= u /\
     v + a <= --s - (&2 / &5) * c ==> s * (u + a) + c * (v + a) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= --s * (u - --(&13 / &50) * s)` THEN
  C1092PRS_PROD `&0 <= c * (--s - (v + a))` THEN
  C1092PRS_PROD `&0 < --s * (a - c)` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `s:real`]);;

let C1092IOFB_LOWER_Y = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\
     u + a <= c - (&14 / &25) * s /\ --(&543 / &500) * c <= v /\
     --s + (&263 / &500) * c < &1
     ==> --(&14 / &25) < s * (u + a) + c * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= --s * ((c - (&14 / &25) * s) - (u + a))` THEN
  C1092PRS_PROD `&0 <= c * (v - --(&543 / &500) * c)` THEN
  C1092PRS_PROD `&0 < c * (a - &1)` THEN
  C1092PRS_PROD `&0 < c * (&1 + s - (&263 / &500) * c)` THEN
  NLIN_TAC ~deg2:false []);;

let C1092IOFB_RIGHT_X = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ c977cc_normal c (--s) /\ s < &0 /\ &1 < a /\
     --(&13 / &50) * s <= u /\ --(&543 / &500) * c <= v
     ==> &1 < c * (u + a) - s * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092PRS_PROD `&0 <= c * (u - --(&13 / &50) * s)` THEN
  C1092PRS_PROD `&0 <= --s * (v - --(&543 / &500) * c)` THEN
  C1092PRS_PROD `&0 < (a - &1) * (c - s)` THEN
  C1092PRS_PROD `&0 <= (&71 / &50 - (c - s)) * (c - s - &1)` THEN
  SUBGOAL_THEN `&1 - &100 / &121 * c * s <= c - s` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092PRS_PROD `&0 < c * --s` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: far_cap *)
let C1092IOFB_FAR_CAP = prove
 (`forall c s u v a cR sR uR vR aR.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092ifsu_negsucc c s u v a /\
     (forall y. --(&14 / &25) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     ldisj c s u v a cR sR uR vR aR
     ==> v + a <= --s - (&14 / &25) * c /\ &237 / &763 < C1092WPS_half c (--s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~linside c s u v a (&1) (--(&14 / &25))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `ldisj c s u v a cR sR uR vR aR` THEN REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1`; `--(&14 / &25)`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s - (&14 / &25) * c` ASSUME_TAC THENL
   [ASM_CASES_TAC `u + a <= c - (&14 / &25) * s` THENL
     [ALL_TAC;
      C1092IFBP_OPEN_TAC THEN
      C1092IFBP_MISS_TAC `~linside c s u v a (&1) (--(&14 / &25))`] THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `a:real`] C1092IOFB_NARROW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `--s`] C1092IOFB_NARROW_SUPPORT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `cR:real`; `sR:real`;
                  `uR:real`; `vR:real`; `aR:real`; `c * (u + a) - s * (v + a)`;
                  `s * (u + a) + c * (v + a)`] C1092IOFB_CROSSING_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[C1092IOFB_UPPER_Y; C1092IOFB_LOWER_Y; C1092IOFB_RIGHT_X] THEN
    MATCH_MP_TAC OCWPVG_VERTEX THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&263 / &500`; `c:real`; `--s`] C1092IFSU_WIDTH_HALF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
    CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN REWRITE_TAC[]]);;
