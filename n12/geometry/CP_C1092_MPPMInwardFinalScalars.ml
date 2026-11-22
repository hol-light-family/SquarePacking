(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalScalars.lean               *)
(* (namespace N12Compact.C1092MPPMInwardFinal).                              *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;               *)
(* Normal: c977cc_normal.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MIFS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

let C1092MIFS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN
     FIRST [ASM_REAL_ARITH_TAC; MATCH_ACCEPT_TAC REAL_LE_POW_2; NLIN_TAC []];
     ALL_TAC]) tms;;

(* introduce w = half c s with its quarter_data identities *)
let C1092MIFS_HALF_TAC c s w =
  let h = list_mk_comb(`C1092WPS_half`,[c;s]) in
  MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term ((=) h)) (concl th) then MP_TAC th else NO_TAC)) THEN
  SPEC_TAC(h,w) THEN GEN_TAC THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

(* Lean: f (definition) *)
let c1092mifs_f = new_definition
 `c1092mifs_f (b:real) (r:real) = (b + r - &1) pow 2 / &2`;;

(* Lean: g (definition) *)
let c1092mifs_g = new_definition
 `c1092mifs_g (b:real) (r:real) = b pow 2 - b + r`;;

(* Lean: fg_bounds *)
let C1092MIFS_FG_BOUNDS = prove
 (`forall b r. c977cc_normal b r
     ==> &0 <= c1092mifs_f b r /\ c1092mifs_f b r <= (&2 / &11) * c1092mifs_g b r /\
         c1092mifs_g b r <= &1 / &2 /\ r - r pow 2 / &2 <= c1092mifs_g b r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN
  C1092MIFS_HALF_TAC `b:real` `r:real` `w:real` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `b + r - &1` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `&11 * ((&1 + w pow 2) pow 2) *
      ((&2 / &11) * (b pow 2 - b + r) - (b + r - &1) pow 2 / &2) =
      &2 * w * (&1 - &3 * w) pow 2 * (&2 - w)` ASSUME_TAC THENL
     [UNDISCH_TAC `(&1 + w pow 2) * b = &1 - w pow 2` THEN
      UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MIFS_PROD_TAC [`&0 <= &2 * w`; `&0 <= (&1 - &3 * w) pow 2 * (&2 - w)`] THEN
    C1092MIFS_PROD_TAC [`&0 <= (&2 * w) * ((&1 - &3 * w) pow 2 * (&2 - w))`] THEN
    SUBGOAL_THEN `&0 < &11 * (&1 + w pow 2) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
        MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIFS_PROD_TAC
     [`&0 < (&11 * (&1 + w pow 2) pow 2) *
            ((b + r - &1) pow 2 / &2 - (&2 / &11) * (b pow 2 - b + r))`] THEN
    ASM_REAL_ARITH_TAC;
    C1092MIFS_PROD_TAC [`&0 <= (b - r) * (&1 - (b + r) / &2)`] THEN NLIN_TAC [];
    NLIN_TAC [SQ_NONNEG `&1 - b`]]);;

(* Lean: g_positive *)
let C1092MIFS_G_POSITIVE = prove
 (`forall b r. c977cc_normal b r /\ &0 < r ==> &0 < c1092mifs_g b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_FG_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_PROD_TAC [`&0 < r * (&1 - r / &2)`] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `r - r pow 2 / &2 <= c1092mifs_g b r` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: g_lower *)
let C1092MIFS_G_LOWER = prove
 (`forall b r. c977cc_normal b r /\ &8 / &17 <= r ==> &104 / &289 <= c1092mifs_g b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_FG_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_PROD_TAC [`&0 <= (r - &8 / &17) * (&1 - (r + &8 / &17) / &2)`] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `r - r pow 2 / &2 <= c1092mifs_g b r` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: predecessor_angle *)
let C1092MIFS_PREDECESSOR_ANGLE = prove
 (`forall b r. c977cc_normal b r /\ &1 < r + (&3 / &5) * b
     ==> &1 / &4 < C1092WPS_half b r /\ b < &15 / &17 /\ &8 / &17 < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `b:real` `r:real` `w:real` THEN
  SUBGOAL_THEN `&0 < &1 + w pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + w pow 2) * (r + (&3 / &5) * b - &1) =
                (&2 / &5) * (&1 - w) * (&4 * w - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + w pow 2) * b = &1 - w pow 2` THEN
    UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 < (&1 + w pow 2) * (r + (&3 / &5) * b - &1)`] THEN
  SUBGOAL_THEN `&1 / &4 < w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MIFS_PROD_TAC [`&0 <= (&1 - w) * (&1 - &4 * w)`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MIFS_PROD_TAC [`&0 < (w - &1 / &4) * (w + &1 / &4)`;
                      `&0 < (w - &1 / &4) * (&4 - w)`] THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [C1092MIFS_PROD_TAC [`&0 <= (&1 + w pow 2) * (b - &15 / &17)`];
    C1092MIFS_PROD_TAC [`&0 <= (&1 + w pow 2) * (&8 / &17 - r)`]] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: relative_order *)
let C1092MIFS_RELATIVE_ORDER = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\
             C1092WPS_half c s < C1092WPS_half b r
     ==> &0 < c * r - s * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  C1092MIFS_HALF_TAC `b:real` `r:real` `w:real` THEN
  SUBGOAL_THEN `(&1 + x pow 2) * (&1 + w pow 2) * (c * r - s * b) =
                &2 * (w - x) * (&1 + w * x)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + w pow 2) * b = &1 - w pow 2` THEN
    UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= w * x`] THEN
  C1092MIFS_PROD_TAC [`&0 < (&2 * (w - x)) * (&1 + w * x)`;
                      `&0 < (&1 + x pow 2) * (&1 + w pow 2)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFS_PROD_TAC [`&0 <= ((&1 + x pow 2) * (&1 + w pow 2)) * --(c * r - s * b)`] THEN
  POP_ASSUM MP_TAC THEN
  UNDISCH_TAC `(&1 + x pow 2) * (&1 + w pow 2) * (c * r - s * b) =
               &2 * (w - x) * (&1 + w * x)` THEN
  UNDISCH_TAC `&0 < (&2 * (w - x)) * (&1 + w * x)` THEN REAL_ARITH_TAC);;

(* Lean: centered_height *)
let C1092MIFS_CENTERED_HEIGHT = prove
 (`forall c s b r H. c977cc_normal c s /\ c977cc_normal b r /\ &0 < r /\ &0 < H /\
               H < c * c1092mifs_f b r - s * c1092mifs_g b r
     ==> H < c / &11 - s / &2 /\ &11 * s < &2 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_FG_BOUNDS) THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_G_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_PROD_TAC [`&0 <= c * ((&2 / &11) * c1092mifs_g b r - c1092mifs_f b r)`] THEN
  SUBGOAL_THEN `&0 < (&2 / &11) * c - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MIFS_PROD_TAC [`&0 <= (s - (&2 / &11) * c) * c1092mifs_g b r`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC
   [`&0 <= ((&2 / &11) * c - s) * (&1 / &2 - c1092mifs_g b r)`] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: centered_cap *)
let C1092MIFS_CENTERED_CAP = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s < &21 / &100
     ==> &0 <= (&7 / &50) * c + s / &2 /\ (&7 / &50) * c + s / &2 < &33 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC
   [`&0 <= (&21 / &100 - x) * (&1 - (&47 / &100) * (x + &21 / &100))`] THEN
  SUBGOAL_THEN `(&1 + x pow 2) * (&33 / &100 - ((&7 / &50) * c + s / &2)) =
                &19 / &100 - x + (&47 / &100) * x pow 2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &19 / &100 - x + (&47 / &100) * x pow 2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFS_PROD_TAC
   [`&0 <= (&1 + x pow 2) * (((&7 / &50) * c + s / &2) - &33 / &100)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: predecessor_margin *)
let C1092MIFS_PREDECESSOR_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ C1092WPS_half c s < &21 / &100
     ==> &0 < &1 - b - r + (c * b + s * r) * (&1 - (&7 / &50) * c - s / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MIFS_CENTERED_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  ABBREV_TAC `D = &1 - (&7 / &50) * c - s / &2` THEN
  SUBGOAL_THEN `&0 <= D /\ D <= &1 /\ &67 / &100 < D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= c * (&1 - D)`; `&0 <= s * (&1 - D)`;
                      `&0 <= ((c + s) - &1) * D`; `&0 <= (c - s) * D`] THEN
  SUBGOAL_THEN `&0 <= &1 - c * D /\ &0 <= &1 - s * D /\
                (&1 - c * D) + (&1 - s * D) < &133 / &100 /\
                (&1 - c * D) - (&1 - s * D) <= &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 <= --((&1 - c * D) - (&1 - s * D)) * (b - r)`;
    `&0 <= ((&1 - c * D) + (&1 - s * D)) * (&10 / &7 - (b + r))`] THEN
  SUBGOAL_THEN `(&1 - c * D) * b + (&1 - s * D) * r < &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: centered_small *)
let C1092MIFS_CENTERED_SMALL = prove
 (`forall c s. c977cc_normal c s /\ &0 < s /\ &11 * s < &2 * c
     ==> &49 / &50 < c /\ s < &9 / &50 /\ C1092WPS_half c s < &91 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_PROD_TAC [`&0 < (&2 * c - &11 * s) * (&2 * c + &11 * s)`] THEN
  SUBGOAL_THEN `&49 / &50 < c /\ s < &9 / &50` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
     [C1092MIFS_PROD_TAC [`&0 <= (&49 / &50 - c) * (&49 / &50 + c)`];
      C1092MIFS_PROD_TAC [`&0 <= (s - &9 / &50) * (s + &9 / &50)`]] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIFS_PROD_TAC [`&0 < (&1 + x pow 2) * (&2 * c - &11 * s)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFS_PROD_TAC [`&0 <= (x - &91 / &1000) * (x + &91 / &1000)`] THEN
  NLIN_TAC ~deg2:false []);;
