(* ========================================================================= *)
(* Port of Compact/Geometry/C977NegativeCorner.lean (Jatloe, N12-jatloe)     *)
(* (namespace N12Compact.C977NegativeCorner).                                *)
(* Full-square support and the actual foreign segment for the negative       *)
(* corner sector.  Lean upper/lower are ABT_upper/ABT_lower; a square with   *)
(* q.s = -t is c s u v a with the hypothesis s = --t.                        *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/C977CornerHalfAngle.ml";;
needs "n12/geometry/C977CornerSupportBounds.ml";;
needs "n12/geometry/C977SingletonSeparation.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let C977NCO_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C977NCO_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let C977NCO_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let C977NCO_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN
                  (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC ORELSE NLIN_TAC []);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: negative_bands *)
let C977NCO_NEGATIVE_BANDS = prove
 (`forall c s u v a t x y. s = --t
     ==> (linside c s u v a x y <=>
          u < c * x - t * y /\ c * x - t * y < u + a /\
          v < t * x + c * y /\ t * x + c * y < v + a)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[linside] THEN
  REWRITE_TAC[REAL_ARITH `c * x + --t * y = c * x - t * y`;
              REAL_ARITH `-- --t * x + c * y = t * x + c * y`]);;

(* Lean: upper_in_bands *)
let C977NCO_UPPER_IN_BANDS = prove
 (`forall c s u v a nx ny.
     ABT_upper c s u v a nx ny =
       (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) +
       a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: lower_in_bands *)
let C977NCO_LOWER_IN_BANDS = prove
 (`forall c s u v a nx ny.
     ABT_lower c s u v a nx ny =
       (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) -
       a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

let C977NCO_ABS_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS; C977NCO_LOWER_IN_BANDS] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[REAL_ARITH `nx * c + ny * --t = nx * c - ny * t`;
              REAL_ARITH `--nx * --t + ny * c = nx * t + ny * c`] THEN
  FIRST_ASSUM(fun th -> try REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 <= x ==> abs x = x`) th]
                        with Failure _ -> REWRITE_TAC[MATCH_MP (REAL_ARITH `x <= &0 ==> abs x = --x`) th]) THEN
  FIRST_X_ASSUM(K ALL_TAC) THEN
  FIRST_ASSUM(fun th -> try REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 <= x ==> abs x = x`) th]
                        with Failure _ -> REWRITE_TAC[MATCH_MP (REAL_ARITH `x <= &0 ==> abs x = --x`) th]) THEN
  REAL_ARITH_TAC;;

(* Lean: upper_negative_pos *)
let C977NCO_UPPER_NEGATIVE_POS = prove
 (`forall c s u v a t nx ny.
     s = --t /\ &0 <= nx * c - ny * t /\ &0 <= nx * t + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c - ny * t) * (u + a) + (nx * t + ny * c) * (v + a)`,
  C977NCO_ABS_TAC);;

(* Lean: upper_negative_nonpos *)
let C977NCO_UPPER_NEGATIVE_NONPOS = prove
 (`forall c s u v a t nx ny.
     s = --t /\ nx * c - ny * t <= &0 /\ &0 <= nx * t + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c - ny * t) * u + (nx * t + ny * c) * (v + a)`,
  C977NCO_ABS_TAC);;

(* Lean: lower_negative_pos *)
let C977NCO_LOWER_NEGATIVE_POS = prove
 (`forall c s u v a t nx ny.
     s = --t /\ &0 <= nx * c - ny * t /\ &0 <= nx * t + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c - ny * t) * u + (nx * t + ny * c) * v`,
  C977NCO_ABS_TAC);;

(* Lean: lower_negative_nonpos *)
let C977NCO_LOWER_NEGATIVE_NONPOS = prove
 (`forall c s u v a t nx ny.
     s = --t /\ nx * c - ny * t <= &0 /\ &0 <= nx * t + ny * c
     ==> ABT_lower c s u v a nx ny =
         (nx * c - ny * t) * (u + a) + (nx * t + ny * c) * v`,
  C977NCO_ABS_TAC);;

(* Lean: corner_face *)
let C977NCO_CORNER_FACE = prove
 (`forall c s u v a t.
     s = --t /\ c977cc_normal c t /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1) (&457 / &500) /\ linside c s u v a (&28 / &25) (&1) /\
     linside c s u v a (&187 / &100) (&19 / &25) /\ ~linside c s u v a (&1) (&1)
     ==> c - t <= u /\ t * (u + a) <= c * v /\ c977cc_boundary c t < v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977NCO_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c * c + --t * --t = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `linside c s u v a x y`) o concl))) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy; REAL_ABS_NEG]) THEN
  SUBGOAL_THEN `abs t = t` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `c - t <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (u + a) <= c * v` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c * c977cc_boundary c t = c + c * t + t * (&1 - t)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_boundary] THEN
   (SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  C977NCO_PROD_TAC `t:real` `u - (c - t)` THEN
  C977NCO_PRODLT_TAC `a - &1` `c + t` THEN
  MATCH_MP_TAC C977CSUP_LT_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: foreign_segment_overlap *)
let C977NCO_FOREIGN_SEGMENT_OVERLAP = prove
 (`forall c s u v a cL sL uL vL aL TT.
     s = --TT /\ c977cc_normal c TT /\ &0 < TT /\ &1 < a /\
     linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2) /\
     v + a <= &2 * (c + TT) /\ c * u + TT * v < &1 /\ u < c - (&28 / &25) * TT /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\ linside cL sL uL vL aL (&1) (&87 / &50)
     ==> exists x y. linside c s u v a x y /\ linside cL sL uL vL aL x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977NCO_NORMAL_TAC THEN
  ABBREV_TAC `lo = (v - TT) / c` THEN ABBREV_TAC `hi = (c - u) / TT` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall y. lo < y <=> v - TT < y * c` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "lo" THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `forall y. y < hi <=> y * TT < c - u` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "hi" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `lo * c = v - TT /\ hi * TT = c - u` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "lo" THEN EXPAND_TAC "hi" THEN CONJ_TAC THEN
   MATCH_MP_TAC REAL_DIV_RMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * TT` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lo < hi` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C977NCO_PROD_TAC `c * TT` `lo - hi` THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&28 / &25 < hi` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lo < &87 / &50` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `y = (max lo (&28 / &25) + min hi (&87 / &50)) / &2` THEN
  SUBGOAL_THEN `lo < y /\ y < hi /\ &28 / &25 < y /\ y < &87 / &50` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "y" THEN
   REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[real_max; real_min] THEN
   REPEAT COND_CASES_TAC THEN REPEAT DISCH_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&1`; `y:real`] THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN
   UNDISCH_TAC `lo < y` THEN UNDISCH_TAC `y < hi` THEN ASM_REWRITE_TAC[] THEN
   REPEAT DISCH_TAC THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `linside c s u v a x y`) o concl))) THEN
   ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
   C977NCO_PROD_TAC `TT:real` `y - &28 / &25` THEN
   C977NCO_PROD_TAC `c:real` `&87 / &50 - y` THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&1`; `&28 / &25`; `&1`; `&87 / &50`; `(&50 / &31) * (y - &28 / &25)`]
    CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `forall P x1 y1 x y. (x1:real) = x /\ (y1:real) = y ==> P x1 y1 ==> P x y`) THEN
  CONJ_TAC THEN REAL_ARITH_TAC);;

let C977NCO_NEG_BANDS = prove
 (`forall c u v a t x y.
     linside c (--t) u v a x y <=>
     u < c * x - t * y /\ c * x - t * y < u + a /\
     v < t * x + c * y /\ t * x + c * y < v + a`,
  MESON_TAC[C977NCO_NEGATIVE_BANDS]);;

let C977NCO_BAND_TAC tm =
  MP_TAC(ASSUME tm) THEN REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC;;

(* Lean: point *)
let C977NCO_POINT = prove
 (`forall cO sO uO vO aO cA sA uA vA aA cL sL uL vL aL t TT.
     sO = --t /\ sA = --TT /\ c977cc_normal cO t /\ c977cc_normal cA TT /\
     &1 < aO /\ aO = aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&1) (&87 / &50) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sA = --TT`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  C977NCO_USE C977NCO_CORNER_FACE [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`; `t:real`] THEN
  C977NCO_USE C977CSUP_POSITIVE_DOT [`cO:real`; `t:real`; `cA:real`; `TT:real`] THEN
  C977NCO_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + --t * --t = &1 /\ cA * cA + --TT * --TT = &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [UNDISCH_TAC `cO pow 2 + t pow 2 = &1`; UNDISCH_TAC `cA pow 2 + TT pow 2 = &1`] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  REFUTE_THEN ASSUME_TAC THEN
  C977NCO_BAND_TAC `linside cA (--TT) uA vA aA (&33 / &20) (&33 / &20)` THEN
  C977NCO_BAND_TAC `linside cA (--TT) uA vA aA (&2) (&87 / &50)` THEN
  C977NCO_BAND_TAC `linside cA (--TT) uA vA aA (&87 / &50) (&2)` THEN
  SUBGOAL_THEN `vA + aA <= &2 * (cA + TT)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cA (--TT) uA vA aA (&2) (&2)` THEN
   REWRITE_TAC[C977NCO_NEG_BANDS] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < TT` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`;
                `cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`]
    C977SS_BOTTOM_ALTERNATIVES) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
   REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC] THENL
  [ASM_CASES_TAC `cO * TT - t * cA <= &0` THENL
   [C977NCO_USE C977NCO_LOWER_NEGATIVE_POS
      [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`; `TT:real`; `t:real`; `cO:real`] THEN
    C977NCO_USE C977CSUP_CORNER_AXIS_BELOW
      [`cO:real`; `t:real`; `cA:real`; `TT:real`; `uA:real`; `vA:real`; `aA:real`] THEN
    RASM_ARITH_TAC;
    C977NCO_USE C977NCO_LOWER_NEGATIVE_NONPOS
      [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`; `TT:real`; `t:real`; `cO:real`] THEN
    C977NCO_USE C977CSUP_REMAINING_SECTION_BOUNDS
      [`cO:real`; `t:real`; `cA:real`; `TT:real`; `uA:real`; `vA:real`; `aA:real`] THEN
    C977NCO_USE C977NCO_FOREIGN_SEGMENT_OVERLAP
      [`cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`;
       `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `TT:real`] THEN
    UNDISCH_TAC `ldisj cA (--TT) uA vA aA cL sL uL vL aL` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
    ASM_REWRITE_TAC[]];
   ASM_CASES_TAC `&0 <= cO * TT - t * cA` THENL
   [C977NCO_USE C977NCO_UPPER_NEGATIVE_POS
      [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`; `t:real`; `TT:real`; `cA:real`] THEN
    C977NCO_USE C977CSUP_OWN_AXIS_ABOVE
      [`cO:real`; `t:real`; `cA:real`; `TT:real`; `uO:real`; `vO:real`; `aO:real`] THEN
    RASM_ARITH_TAC;
    C977NCO_USE C977NCO_UPPER_NEGATIVE_NONPOS
      [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`; `t:real`; `TT:real`; `cA:real`] THEN
    C977NCO_USE C977CSUP_OWN_AXIS_BELOW
      [`cO:real`; `t:real`; `cA:real`; `TT:real`; `uO:real`; `vO:real`; `aO:real`] THEN
    RASM_ARITH_TAC]]);;
