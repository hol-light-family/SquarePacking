(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWallPairAxes.lean (Jatloe, N12-jatloe).    *)
(* Full-square separating-axis reduction for an escaping elbow and its      *)
(* actual right wall.                                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallLongitudinal.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* copy the four face inequalities of a linside assumption *)
let CWPA_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: central_lower_faces *)
let CWPA_CENTRAL_LOWER_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\ &12 * s <= &5 * c /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&2) (&2) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> &2 * c + &2 * s <= u /\
         --(&47 / &20) * s + (&33 / &20) * c <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CWPA_UNFOLD_TAC `linside c s u v a (&2) (&113 / &50)` THEN
  CWPA_UNFOLD_TAC `linside c s u v a (&113 / &50) (&2)` THEN
  CWPA_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&2) (&2)`;
   UNDISCH_TAC `~linside c s u v a (&47 / &20) (&33 / &20)`] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: cosine_bound *)
let CWPA_COSINE_BOUND = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &12 * s <= &5 * c
         ==> &12 / &13 <= c`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&5 * c - &12 * s) * (&5 * c + &12 * s) /\
                &0 < (&12 / &13 - c) * (&12 / &13 + c)` MP_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC);;

(* Lean: wall_angle_order *)
let CWPA_WALL_ANGLE_ORDER = prove
 (`forall c s r t z.
     &12 / &13 <= c /\ &0 <= s /\ &0 < r /\ &0 <= t /\
     c pow 2 + s pow 2 = &1 /\ r pow 2 + t pow 2 = &1 /\
     &0 <= z /\ (&1 + c) * z = s /\
     r * t * z < &1 - r - (&43 / &500) * t pow 2
     ==> s * r < c * t`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (s * r - c * t) * (s * r + c * t)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `c * c - r * r = c * c * t * t - s * s * r * r` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `r * r + t * t = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c <= r` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (c - r) * (c + r)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t <= s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (t - s) * (t + s) /\ &0 <= (r - c) * (r + c)` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `r * r + t * t = &1` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t <= (&1 + r) * z` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= z * (r - c)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(r * t) * t <= (r * t) * ((&1 + r) * z) /\
    (&1 + r) * (r * t * z) < (&1 + r) * (&1 - r - (&43 / &500) * t * t) /\
    &0 <= (t * t) * ((&543 / &500) * r - &457 / &500)` MP_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  UNDISCH_TAC `r * r + t * t = &1` THEN REAL_ARITH_TAC);;

(* one separating-axis case of `alternatives` *)
let CWPA_CASE_TAC nx ny swap radius strict =
  let sep = SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                   `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`; nx; ny]
                  ABT_SEPARATED in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC strict THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RASM_ARITH_TAC;;

(* Lean: alternatives *)
let CWPA_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\
     &0 < cA /\ &0 <= sA /\ &12 * sA <= &5 * cA /\ &0 < cR /\ &0 <= sR /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     &0 <= z /\ z < &2 / &5 /\
     linside cA sA uA vA aA (&3) (&2 + z) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  SUBGOAL_THEN `cA <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sA:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cR * z /\ &0 < cR * (&2 / &5 - z)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWPA_UNFOLD_TAC `linside cA sA uA vA aA (&113 / &50) (&2)` THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aA (&1543 / &500) (&2)` THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aA (&3) (&12 / &5)` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    ABT_OWNU) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    ABT_OWNU) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ASM_REWRITE_TAC[C977CB_faceSep] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [CWPA_CASE_TAC `cA:real` `sA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cR:real`; `sR:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     (SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
             `&1543 / &500`; `&2`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS);
   CWPA_CASE_TAC `--sA:real` `cA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cR:real`; `sR:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     (SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
             `&3`; `&12 / &5`; `--sA:real`; `cA:real`] ABT_STRICT_BOUNDS);
   CWPA_CASE_TAC `cR:real` `sR:real` true
     (SPECL [`cR:real`; `sR:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
             `&113 / &50`; `&2`; `cR:real`; `sR:real`] ABT_STRICT_BOUNDS);
   CWPA_CASE_TAC `--sR:real` `cR:real` true
     (SPECL [`cR:real`; `sR:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
             `&3`; `&2 + z`; `--sR:real`; `cR:real`] ABT_STRICT_BOUNDS)]);;
