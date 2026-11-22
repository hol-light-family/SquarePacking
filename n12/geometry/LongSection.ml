(* ========================================================================= *)
(* Port of Compact/Geometry/LongSection.lean (Jatloe, N12-jatloe).            *)
(* A square of side a > 1 has an open horizontal section of length          *)
(* (a+1)/2 > 1 whenever the cut is within (|c|+|s|-2|cs|)/2 of its centre.   *)
(* Also ports turnFrame and its simp lemmas from source/S12/WallGeometry.    *)
(* turnFrame (c,s,u,v,a) is the 5-tuple (--s, c, v, --u - a, a).             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SectionCapacity.ml";;

(* Lean: sectionRadius (definition; depends only on the frame c, s) *)
let lsec_radius = new_definition
 `lsec_radius (c:real) (s:real) = (abs c + abs s - &2 * abs(c * s)) / &2`;;

(* Lean: S12.turnFrame_inside (source/S12/WallGeometry.lean) *)
let LSEC_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: S12.turnFrame unit_normal / side_pos fields *)
let LSEC_TURN_SQUARE = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 < a
           ==> --s * --s + c * c = &1 /\ &0 < a`,
  REAL_ARITH_TAC);;

(* Lean: S12.turnFrame_centerX, S12.turnFrame_centerY *)
let LSEC_TURN_CENTRE = prove
 (`forall c s u v a. lcx (--s) c v (--u - a) a = lcx c s u v a /\
               lcy (--s) c v (--u - a) a = lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: sectionRadius_turnFrame *)
let LSEC_RADIUS_TURN = prove
 (`forall c s. lsec_radius (--s) c = lsec_radius c s`,
  REWRITE_TAC[lsec_radius; REAL_ABS_NEG; REAL_MUL_LNEG] THEN REAL_ARITH_TAC);;

(* Lean: positive_frame_radius *)
let LSEC_POSITIVE_FRAME_RADIUS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 <= c' /\ &0 <= s' /\ a' = a /\
           lcy c' s' u' v' a' = lcy c s u v a /\
           lsec_radius c' s' = lsec_radius c s /\
           forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y`,
  let fin = REWRITE_TAC[linside; lcy; lsec_radius; REAL_ABS_NEG;
                        REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
            ASM_REAL_ARITH_TAC in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c` THEN ASM_CASES_TAC `&0 <= s` THENL
  [MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
   ASM_REWRITE_TAC[];
   MAP_EVERY EXISTS_TAC [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`] THEN
   fin;
   MAP_EVERY EXISTS_TAC [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`] THEN
   fin;
   MAP_EVERY EXISTS_TAC [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`] THEN
   fin]);;

(* Lean: scalar_long_section  (InBands lo lo a p q written out) *)
let LSEC_SCALAR_LONG_SECTION = prove
 (`forall a c s t. &1 < a /\ &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
             abs t <= (c + s - &2 * c * s) / &2
     ==> exists z. forall d. abs d < (a + &1) / &4
           ==> --a / &2 < c * (z + d) + s * t /\
               c * (z + d) + s * t < --a / &2 + a /\
               --a / &2 < --s * (z + d) + c * t /\
               --s * (z + d) + c * t < --a / &2 + a`,
  REWRITE_TAC[REAL_POW_2; REAL_ABS_BOUNDS] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c * s <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c + s - &2 * c * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `c + s = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c * s = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c + s) * (c + s) = &1` MP_TAC THENL
    [ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists lam. lam * (c + s - &2 * c * s) = t` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `t / (c + s - &2 * c * s)` THEN
   ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1 / &2) <= lam /\ lam <= &1 / &2` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  EXISTS_TAC `c * (&1 - c) * lam - s * (&1 - s) * lam` THEN
  X_GEN_TAC `d:real` THEN REWRITE_TAC[GSYM REAL_BOUNDS_LT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((c * (&1 - c) * lam - s * (&1 - s) * lam) + d) + s * t =
      (&1 - c) * lam + c * d /\
    --s * ((c * (&1 - c) * lam - s * (&1 - s) * lam) + d) + c * t =
      (&1 - s) * lam - s * d`
  (fun th -> REWRITE_TAC[th]) THENL
  [UNDISCH_TAC `lam * (c + s - &2 * c * s) = t` THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a - &1) * (&2 - c) /\ &0 < (a - &1) * (&2 - s)`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: positive_frame_long_section *)
let LSEC_POSITIVE_FRAME_LONG_SECTION = prove
 (`forall c s u v a h. c * c + s * s = &1 /\ &0 < a /\
                 &1 < a /\ &0 <= c /\ &0 <= s /\
                 abs(h - lcy c s u v a) <= (c + s - &2 * c * s) / &2
     ==> scap_longsec c s u v a h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `c:real`; `s:real`; `h - lcy c s u v a`]
    LSEC_SCALAR_LONG_SECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real`) THEN
  REWRITE_TAC[scap_longsec] THEN
  MAP_EVERY EXISTS_TAC [`lcx c s u v a + z - (a + &1) / &4`;
                        `lcx c s u v a + z + (a + &1) / &4`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x - (lcx c s u v a + z)`) THEN
  ANTS_TAC THENL [REWRITE_TAC[GSYM REAL_BOUNDS_LT] THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[linside] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REAL_ARITH_TAC);;

(* Lean: horizontal_long_section *)
let LSEC_HORIZONTAL_LONG_SECTION = prove
 (`forall c s u v a h. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
                 abs(h - lcy c s u v a) <= lsec_radius c s
     ==> scap_longsec c s u v a h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    LSEC_POSITIVE_FRAME_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `h:real`]
    LSEC_POSITIVE_FRAME_LONG_SECTION) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `lsec_radius c' s' = (c' + s' - &2 * c' * s') / &2` MP_TAC THENL
   [REWRITE_TAC[lsec_radius; REAL_ABS_MUL] THEN
    ASM_REWRITE_TAC[real_abs] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   ASM_REWRITE_TAC[scap_longsec]]);;
