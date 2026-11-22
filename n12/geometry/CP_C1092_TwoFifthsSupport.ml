(* ========================================================================= *)
(* Port of Compact/Completion/C1092/TwoFifthsSupport.lean                    *)
(* (N12Compact.C1092TwoFifths.Support).  Whole-square supports and the       *)
(* exhaustive directed separator sources for the two-fifths squeeze.         *)
(* upper / lower are ABT_upper / ABT_lower; supportRadius is                 *)
(* tss_support_radius; square_support_bound is                              *)
(* C1092MPWS_SQUARE_SUPPORT_BOUND.                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsData.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;

(* Lean: upper_pos_pos *)
let C1092TFSU_UPPER_POS_POS = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ &0 <= e
     ==> ABT_upper c s u v a nx ny = d * (u + a) + e * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`] THEN REAL_ARITH_TAC);;

(* Lean: upper_pos_neg *)
let C1092TFSU_UPPER_POS_NEG = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ e <= &0
     ==> ABT_upper c s u v a nx ny = d * (u + a) + e * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`;
               REAL_ARITH `d <= &0 ==> max d (&0) = &0`] THEN REAL_ARITH_TAC);;

(* Lean: upper_neg_neg *)
let C1092TFSU_UPPER_NEG_NEG = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ d <= &0 /\ e <= &0
     ==> ABT_upper c s u v a nx ny = d * u + e * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `d <= &0 ==> max d (&0) = &0`] THEN REAL_ARITH_TAC);;

(* Lean: radius_even *)
let C1092TFSU_RADIUS_EVEN = prove
 (`forall c s a nx ny. tss_support_radius c s a (--nx) (--ny) = tss_support_radius c s a nx ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tss_support_radius] THEN
  REWRITE_TAC[REAL_ARITH `--nx * c + --ny * s = --(nx * c + ny * s)`;
              REAL_ARITH `-- --nx * s + --ny * c = --(--nx * s + ny * c)`; REAL_ABS_NEG]);;

(* Lean: upper_neg *)
let C1092TFSU_UPPER_NEG = prove
 (`forall c s u v a nx ny. ABT_upper c s u v a (--nx) (--ny) = --ABT_lower c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower; C1092TFSU_RADIUS_EVEN] THEN REAL_ARITH_TAC);;

(* Lean: lower_neg *)
let C1092TFSU_LOWER_NEG = prove
 (`forall c s u v a nx ny. ABT_lower c s u v a (--nx) (--ny) = --ABT_upper c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower; C1092TFSU_RADIUS_EVEN] THEN REAL_ARITH_TAC);;

(* Lean: reverse *)
let C1092TFSU_REVERSE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR nx ny.
     ABT_upper cR sR uR vR aR nx ny <= ABT_lower cA sA uA vA aA nx ny
     ==> ABT_upper cA sA uA vA aA (--nx) (--ny) <= ABT_lower cR sR uR vR aR (--nx) (--ny)`,
  REWRITE_TAC[C1092TFSU_UPPER_NEG; C1092TFSU_LOWER_NEG] THEN REAL_ARITH_TAC);;

(* Lean: rightward *)
let C1092TFSU_RIGHTWARD = prove
 (`forall cA sA uA vA aA cR sR uR vR aR x y nx ny.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     nx pow 2 + ny pow 2 = &1 /\ linside cA sA uA vA aA x y /\
     linside cR sR uR vR aR (&1) y /\ x < &1 /\
     ABT_upper cA sA uA vA aA nx ny <= ABT_lower cR sR uR vR aR nx ny
     ==> &0 < nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `x:real`; `y:real`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&1`; `y:real`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= --nx * (&1 - x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* the opposite transverse face: lower R s (-c) = -(v + a) *)
let C1092TFSU_LOWER_OPPOSITE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> ABT_lower c s u v a s (--c) = --(v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `s:real`; `--c:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[REAL_ARITH `s * c + --c * s = &0`;
              REAL_ARITH `--s * s + --c * c = --(c * c + s * s)`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_min] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let C1092TFSU_UNIT_TAC =
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  ASM_REAL_ARITH_TAC;;

(* rightward on the newest case hypothesis (optionally reversed), closing by contradiction *)
let C1092TFSU_CONE_TAC rev nx ny =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
                  `x:real`; `y:real`; nx; ny] C1092TFSU_RIGHTWARD) THEN
    ASM_REWRITE_TAC[th']) THEN
  ANTS_TAC THENL [C1092TFSU_UNIT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN RASM_ARITH_TAC;;

let C1092TFSU_TAKE_TAC rev =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC th') THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];;

(* Lean: candidates (private) *)
let C1092TFSU_CANDIDATES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR x y.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     aA = aR /\ &0 < cA /\ &0 <= sA /\ &0 < cR /\
     linside cA sA uA vA aA x y /\ linside cR sR uR vR aR (&1) y /\ x < &1 /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA sA (--cA) <= ABT_lower cR sR uR vR aR sA (--cA) \/
         ABT_upper cA sA uA vA aA cR sR <= uR \/
         ABT_upper cA sA uA vA aA (--sR) cR <= vR \/
         ABT_upper cA sA uA vA aA sR (--cR) <= --(vR + aR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    C1092TFSU_LOWER_OPPOSITE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [C1092TFSU_TAKE_TAC false;
    C1092TFSU_CONE_TAC true `--cA` `--sA`;
    C1092TFSU_CONE_TAC false `--sA` `cA:real`;
    C1092TFSU_TAKE_TAC true;
    C1092TFSU_TAKE_TAC false;
    C1092TFSU_CONE_TAC true `--cR` `--sR`;
    C1092TFSU_TAKE_TAC false;
    C1092TFSU_TAKE_TAC true]);;

(* Lean: negative_axes *)
let C1092TFSU_NEGATIVE_AXES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR x y.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     aA = aR /\ &0 < cA /\ &0 <= sA /\ &0 < cR /\ sR <= &0 /\
     linside cA sA uA vA aA x y /\ linside cR sR uR vR aR (&1) y /\ x < &1 /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA sA (--cA) <= ABT_lower cR sR uR vR aR sA (--cA) \/
         ABT_upper cA sA uA vA aA cR sR <= uR \/
         ABT_upper cA sA uA vA aA (--sR) cR <= vR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
                `x:real`; `y:real`] C1092TFSU_CANDIDATES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~e ==> (a \/ b \/ c \/ d \/ e) ==> (a \/ b \/ c \/ d)`) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    C1092TFSU_LOWER_OPPOSITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
                `x:real`; `y:real`; `sR:real`; `--cR`] C1092TFSU_RIGHTWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092TFSU_UNIT_TAC; DISCH_TAC THEN RASM_ARITH_TAC]);;

(* Lean: positive_axes *)
let C1092TFSU_POSITIVE_AXES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR x y.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     aA = aR /\ &0 < cA /\ &0 <= sA /\ &0 < cR /\ &0 <= sR /\
     linside cA sA uA vA aA x y /\ linside cR sR uR vR aR (&1) y /\ x < &1 /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA sA (--cA) <= ABT_lower cR sR uR vR aR sA (--cA) \/
         ABT_upper cA sA uA vA aA cR sR <= uR \/
         ABT_upper cA sA uA vA aA sR (--cR) <= --(vR + aR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
                `x:real`; `y:real`] C1092TFSU_CANDIDATES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~d ==> (a \/ b \/ c \/ d \/ e) ==> (a \/ b \/ c \/ e)`) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
                `x:real`; `y:real`; `--sR`; `cR:real`] C1092TFSU_RIGHTWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092TFSU_UNIT_TAC; DISCH_TAC THEN RASM_ARITH_TAC]);;

(* Lean: wall_lower *)
let C1092TFSU_WALL_LOWER = prove
 (`forall c s u v a nx ny.
     c * c + s * s = &1 /\ &0 < a /\
     C1092TF_right c s u v a /\ &0 <= c /\ &0 <= nx /\ ny <= &0
     ==> ABT_lower c s u v a nx ny <=
         &2 * nx - a * (nx * (c + abs s) + abs(nx * c + ny * s) +
                        abs(--nx * s + ny * c)) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C1092TF_right] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `&2`]
    C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[tss_support_radius; REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID;
              REAL_ADD_LID; REAL_MUL_LNEG; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= nx * (&2 - (lcx c s u v a + a / &2 * (c + abs s)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --ny * lcy c s u v a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ABT_lower; tss_support_radius] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
