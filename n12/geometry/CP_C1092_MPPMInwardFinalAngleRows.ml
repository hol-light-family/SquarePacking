(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalAngleRows.lean            *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  The three positive-         *)
(* predecessor rows and both relative negative rows of the centered angle    *)
(* proof (exact polynomial remainders on the complete intervals).            *)
(* Normal: c977cc_normal; half / quarter_data: C1092WPS_half /               *)
(* C1092WPS_QUARTER_DATA; normal_bounds: C977CC_NORMAL_BOUNDS;               *)
(* canonical_half_bounds: C1092IFAS_CANONICAL_HALF_BOUNDS; half_cross:       *)
(* C1092MIFE_HALF_CROSS; coordinates_after: C1092MIFSS_COORDINATES_AFTER;    *)
(* cap_f0 / cap_g0 / cap_negative_fg: C1092IFCS_CAP_F0 / _G0 / _NEGATIVE_FG; *)
(* f / g: c1092mifs_f / c1092mifs_g.  The field_simp identities are proved   *)
(* by REAL_RING from the quarter_data relations (1+w^2) b = 1-w^2,           *)
(* (1+w^2) r = 2 w.  Tag C1092IFAR_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalAngleScalars.ml";;

(* Lean: angleFz, angleGz, angleFl, angleGl *)
let c1092ifar_angleFz = new_definition
 `c1092ifar_angleFz (b:real) (r:real) =
    (&543 / &500) * b pow 2 + (&7 / &20) * r pow 2 - (&7 / &20) * b * r - b`;;
let c1092ifar_angleGz = new_definition
 `c1092ifar_angleGz (b:real) (r:real) = (&7 / &20) * b pow 2 + (&92 / &125) * b * r - r`;;
let c1092ifar_angleFl = new_definition
 `c1092ifar_angleFl (b:real) (r:real) =
    (&543 / &500) * b pow 2 + (&7 / &20) * b * r + (&7 / &20) * r pow 2 - b`;;
let c1092ifar_angleGl = new_definition
 `c1092ifar_angleGl (b:real) (r:real) = (&7 / &20) * b pow 2 - (&92 / &125) * b * r + r`;;

(* Lean: rational_frame (private) *)
let C1092IFAR_RATIONAL_FRAME = prove
 (`forall b r. c977cc_normal b r
     ==> b = (&1 - C1092WPS_half b r pow 2) / (&1 + C1092WPS_half b r pow 2) /\
         r = (&2 * C1092WPS_half b r) / (&1 + C1092WPS_half b r pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `b:real` `r:real` `w:real` THEN
  SUBGOAL_THEN `&0 < &1 + w pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* the lemma prelude: strip both normals, introduce w = half b r with bounds *)
let C1092IFAR_PRELUDE_TAC =
  FIRST_ASSUM(fun th -> if concl th = `c977cc_normal b r`
                        then MP_TAC(MATCH_MP C1092IFAS_CANONICAL_HALF_BOUNDS th) else NO_TAC) THEN
  DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `b:real` `r:real` `w:real` THEN
  SUBGOAL_THEN `&0 < &1 + w pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC];;

(* the field_simp identities: ring consequences of the quarter_data relations *)
let C1092IFAR_RING_TAC =
  UNDISCH_TAC `(&1 + w pow 2) * b = &1 - w pow 2` THEN
  UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN CONV_TAC REAL_RING;;

(* Lean: angle_z_row *)
let C1092IFAR_ANGLE_Z_ROW = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ (&2 / &5) * c <= s
     ==> c * c1092ifar_angleFz b r - s * c1092ifar_angleGz b r <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IFAR_PRELUDE_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= (&5 / &12 - w) * (&5 / &12 + w)`] THEN
  SUBGOAL_THEN `w pow 2 <= &25 / &144` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= (&5 / &12 - w) * w pow 2`] THEN
  SUBGOAL_THEN `w pow 3 <= &125 / &1728` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4865 * w pow 3 + &5222 * w pow 2 <= &1260` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= w * (&1260 - (&4865 * w pow 3 + &5222 * w pow 2))`] THEN
  SUBGOAL_THEN `&4865 * w pow 4 + &5222 * w pow 3 - &1230 * w pow 2 - &1222 * w - &135 < &0`
    ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2500 * (&1 + w pow 2) pow 2 *
                (c1092ifar_angleFz b r - (&2 / &5) * c1092ifar_angleGz b r) =
                &4865 * w pow 4 + &5222 * w pow 3 - &1230 * w pow 2 - &1222 * w - &135`
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092ifar_angleFz; c1092ifar_angleGz] THEN C1092IFAR_RING_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092ifar_angleFz b r - (&2 / &5) * c1092ifar_angleGz b r < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&2500 * (&1 + w pow 2) pow 2) *
                  (c1092ifar_angleFz b r - (&2 / &5) * c1092ifar_angleGz b r)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c1092ifar_angleGz b r` THENL
   [C1092MIFS_PROD_TAC [`&0 < c * --(c1092ifar_angleFz b r - (&2 / &5) * c1092ifar_angleGz b r)`;
                        `&0 <= (s - (&2 / &5) * c) * c1092ifar_angleGz b r`] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `c1092ifar_angleFz b r - c1092ifar_angleGz b r =
                  (b - r) * ((&92 / &125) * b - (&7 / &20) * r - &1)` ASSUME_TAC THENL
     [REWRITE_TAC[c1092ifar_angleFz; c1092ifar_angleGz] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092MIFS_PROD_TAC [`&0 <= (b - r) * --((&92 / &125) * b - (&7 / &20) * r - &1)`;
                        `&0 <= (c - s) * --(c1092ifar_angleGz b r)`] THEN
    SUBGOAL_THEN `c1092ifar_angleFz b r - c1092ifar_angleGz b r <= &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MIFS_PROD_TAC [`&0 <= c * --(c1092ifar_angleFz b r - c1092ifar_angleGz b r)`] THEN
    RASM_ARITH_TAC]);;

(* Lean: angle_f0_row *)
let C1092IFAR_ANGLE_F0_ROW = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ (&2 / &5) * c <= s
     ==> c * ((b + r - &1) pow 2 / &2 + (&43 / &500) * r pow 2) -
         s * (r pow 2 + b - r - (&43 / &500) * b * r) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092IFCS_CAP_F0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= (b - r) * (&2 - b - r)`] THEN
  SUBGOAL_THEN `b * r <= &1 / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `b - r:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&457 / &1000 <= r pow 2 + b - r - (&43 / &500) * b * r` ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `&0 <= (b - r) * (&2 - b - r)` THEN
    UNDISCH_TAC `b * r <= &1 / &2` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `F0 = (b + r - &1) pow 2 / &2 + (&43 / &500) * r pow 2` THEN
  ABBREV_TAC `L0 = r pow 2 + b - r - (&43 / &500) * b * r` THEN
  C1092MIFS_PROD_TAC [`&0 < c * (&13 / &100 - F0)`; `&0 <= s * (L0 - &457 / &1000)`] THEN
  RASM_ARITH_TAC);;

(* Lean: angle_g0_row *)
let C1092IFAR_ANGLE_G0_ROW = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ (&2 / &5) * c <= s /\
             C1092WPS_half b r < &43 / &500 /\ b + r < &29 / &25
     ==> c * (&43 / &500 + (b + r - &1) pow 2 / &2) - s * (r pow 2 + b - r) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092IFCS_CAP_G0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&248151 / &251849) (&43000 / &251849)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half (&248151 / &251849) (&43000 / &251849) = &43 / &500` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `&248151 / &251849`; `&43000 / &251849`]
    C1092MIFE_HALF_CROSS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&248151 / &251849`; `&43000 / &251849`; `b:real`; `r:real`]
    C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&101 / &125 < r pow 2 + b - r` ASSUME_TAC THENL
   [MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G0 = &43 / &500 + (b + r - &1) pow 2 / &2` THEN
  ABBREV_TAC `L0 = r pow 2 + b - r` THEN
  C1092MIFS_PROD_TAC [`&0 < c * (&247 / &2500 - G0)`; `&0 <= s * (L0 - &101 / &125)`] THEN
  RASM_ARITH_TAC);;

(* Lean: angle_left_row *)
let C1092IFAR_ANGLE_LEFT_ROW = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ (&7 / &16) * c <= s
     ==> c * c1092ifar_angleFl b r - s * c1092ifar_angleGl b r < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IFAR_PRELUDE_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1092ifar_angleGl b r` ASSUME_TAC THENL
   [C1092MIFS_PROD_TAC [`&0 <= r * (&1 - (&92 / &125) * b)`;
                        `&0 <= (b - &7 / &10) * (b + &7 / &10)`] THEN
    REWRITE_TAC[c1092ifar_angleGl] THEN REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = w - &1 / &4` THEN
  SUBGOAL_THEN `--(&1 / &4) <= h /\ h <= &1 / &6` STRIP_ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= (&1 / &4 - h) * (&1 / &4 + h)`] THEN
  SUBGOAL_THEN `&15463 * h pow 2 - &2289 * h - &60123 / &8 <= &0` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h pow 2 * (&15463 * h pow 2 - &2289 * h - &60123 / &8) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&12505 / &256) - (&7569 / &16) * h - &3726 * h pow 2 < &0` ASSUME_TAC THENL
   [MP_TAC(SPEC `&7452 * h + &7569 / &16` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&15463 * w pow 4 - &17752 * w pow 3 - &3726 * w pow 2 + &3752 * w - &537 =
                --(&12505 / &256) - (&7569 / &16) * h - &3726 * h pow 2 +
                h pow 2 * (&15463 * h pow 2 - &2289 * h - &60123 / &8)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&15463 * w pow 4 - &17752 * w pow 3 - &3726 * w pow 2 + &3752 * w - &537 < &0`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&8000 * (&1 + w pow 2) pow 2 *
                (c1092ifar_angleFl b r - (&7 / &16) * c1092ifar_angleGl b r) =
                &15463 * w pow 4 - &17752 * w pow 3 - &3726 * w pow 2 + &3752 * w - &537`
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092ifar_angleFl; c1092ifar_angleGl] THEN C1092IFAR_RING_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092ifar_angleFl b r - (&7 / &16) * c1092ifar_angleGl b r < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&8000 * (&1 + w pow 2) pow 2) *
                  (c1092ifar_angleFl b r - (&7 / &16) * c1092ifar_angleGl b r)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 < c * --(c1092ifar_angleFl b r - (&7 / &16) * c1092ifar_angleGl b r)`;
                      `&0 <= (s - (&7 / &16) * c) * c1092ifar_angleGl b r`] THEN
  RASM_ARITH_TAC);;

(* Lean: angle_right_row *)
let C1092IFAR_ANGLE_RIGHT_ROW = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ (&7 / &16) * c <= s /\
             &21 / &100 <= C1092WPS_half b r
     ==> c * ((&43 / &500) * b pow 2 + c1092mifs_f b r) -
         s * (c1092mifs_g b r - (&43 / &500) * b * r) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092IFCS_CAP_NEGATIVE_FG) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN C1092IFAR_PRELUDE_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= w * (&5 / &12 - w)`] THEN
  ABBREV_TAC `R = &4844 * w pow 2 + (&9688 * (&21 / &100) - &19801) * w +
                  &14532 * (&21 / &100) pow 2 - &39602 * (&21 / &100) + &10812` THEN
  SUBGOAL_THEN `R < &0` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `P = &4844 * w pow 4 - &19801 * w pow 3 + &10812 * w pow 2 - &3199 * w + &344` THEN
  SUBGOAL_THEN `P = (&4844 * (&21 / &100) pow 4 - &19801 * (&21 / &100) pow 3 +
                     &10812 * (&21 / &100) pow 2 - &3199 * (&21 / &100) + &344) +
                    (w - &21 / &100) * (&19376 * (&21 / &100) pow 3 - &59403 * (&21 / &100) pow 2 +
                                        &21624 * (&21 / &100) - &3199) +
                    (w - &21 / &100) pow 2 * R` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN EXPAND_TAC "R" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV REAL_RAT_REDUCE_CONV)) THEN
  SUBGOAL_THEN `(w - &21 / &100) pow 2 * R <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `P < &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4000 * (&1 + w pow 2) pow 2 *
                ((&43 / &500) * b pow 2 + c1092mifs_f b r -
                 (&7 / &16) * (c1092mifs_g b r - (&43 / &500) * b * r)) = P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN C1092IFAR_RING_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&43 / &500) * b pow 2 + c1092mifs_f b r -
                (&7 / &16) * (c1092mifs_g b r - (&43 / &500) * b * r) < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&4000 * (&1 + w pow 2) pow 2) *
                  ((&43 / &500) * b pow 2 + c1092mifs_f b r -
                   (&7 / &16) * (c1092mifs_g b r - (&43 / &500) * b * r))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `N = (&43 / &500) * b pow 2 + c1092mifs_f b r` THEN
  ABBREV_TAC `M = c1092mifs_g b r - (&43 / &500) * b * r` THEN
  C1092MIFS_PROD_TAC [`&0 < c * --(N - (&7 / &16) * M)`; `&0 <= (s - (&7 / &16) * c) * M`] THEN
  RASM_ARITH_TAC);;
