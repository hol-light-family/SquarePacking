(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NorthwestHalfpoint.lean        *)
(* (namespace N12Compact.FiniteCases.C972).  An NE-owned top origin forces   *)
(* the actual NW outer halfpoint.  owners p i = owner of mask EL i           *)
(* c972o_masks, written with the literal mask (owners 0..11 = masks 1,2,12,  *)
(* 48,192,256,512,1024,2048,4096,8192,16384).  fixed = C972CS_FIXED          *)
(* (C972CS_FIXED_TAC), foreign = C972CS_CLASH_TAC.  A Lean OpenSquare q is   *)
(* c s u v a with its unit normal explicit; (pullX q).translated 2 2 is the  *)
(* tuple c972nh_tr22 (c972ur_px q) (C972NF_TRANSLATED, LINSIDE_PULLX).       *)
(* LowerSegmentSupport.support = CCLSS_SUPPORT, CanonicalScalars.bounds =    *)
(* CCCS_BOUNDS, ClosedFrames.canonical_frame = CLF_CANONICAL_FRAME,          *)
(* northeast_upper_anchor = C972NF_NORTHEAST_UPPER_ANCHOR, left_bar =        *)
(* C972MC_LEFT_BAR, left_missing_impossible = C972MC_LEFT_MISSING_IMPOSSIBLE.*)
(* Tag C972NH_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NorthwestForward.ml";;
needs "n12/geometry/CP_CommonCases_LowerSegmentSupport.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let c972nh_own = c972mc_own and c972nh_stmt = c972mc_stmt and c972nh_tuple = c972mc_tuple;;

(* q.translated 2 2 of a 5-tuple *)
let c972nh_tr22 t = match t with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`])
                         [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`; `a:real`]
  | _ -> failwith "c972nh_tr22";;

(* positive linside assumptions -> their four band inequalities *)
let C972NH_UNFOLD_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_comb t && fst (strip_comb t) = `linside`
    then STRIP_ASSUME_TAC(REWRITE_RULE[linside] th) else NO_TAC));;

(* linear arithmetic over the real assumptions (LP based, no Fourier-Motzkin blow-up) *)
let C972NH_LIN =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

(* goal  ~(band conjunction) ==> F  (or the conjunction itself): prove the bands *)
let C972NH_BANDS_TAC =
  REWRITE_TAC[linside] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  TRY(DISCH_THEN(MATCH_MP_TAC o MATCH_MP (TAUT `~p ==> p ==> false`))) THEN C972NH_LIN;;

(* a contradiction (goal F) from the omitted point tm *)
let C972NH_OMIT_TAC tm = UNDISCH_TAC tm THEN C972NH_BANDS_TAC;;

(* Lean: shallow_projection (private) *)
let C972NH_SHALLOW_PROJECTION = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &17 * s <= &5 * c
         ==> &17 / &20 * c + &13 / &20 * s < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&17 * c + &5 * s) * (&17 * c + &5 * s) <= &314` ASSUME_TAC THENL
   [MP_TAC(SPEC `&5 * c - &17 * s` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&17 * c + &5 * s < &3140 / &177` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    SUBGOAL_THEN `&0 <= (&17 * c + &5 * s - &3140 / &177) * (&17 * c + &5 * s + &3140 / &177)`
      MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN C972NH_LIN;
      UNDISCH_TAC `(&17 * c + &5 * s) * (&17 * c + &5 * s) <= &314` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  C972NH_LIN);;

(* Lean: northwest_positive_half (private) *)
let C972NH_POSITIVE_HALF = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&2 / &5) (&1) /\ linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\ ~linside c s u v a (--(&1 / &10)) (&3 / &5)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NH_UNFOLD_TAC THEN
  SUBGOAL_THEN `&17 * s < &5 * c` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    C972NH_OMIT_TAC `~linside c s u v a (--(&1 / &10)) (&3 / &5)`;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &20) * c + &7 / &20 * s <= u` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    C972NH_OMIT_TAC `~linside c s u v a (--(&7 / &20)) (&7 / &20)`;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C972NH_SHALLOW_PROJECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN ANTS_TAC THENL [C972NH_LIN; DISCH_TAC] THEN
  REWRITE_TAC[linside] THEN C972NH_LIN);;

(* Lean: right_support (private) *)
let C972NH_RIGHT_SUPPORT = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ s = --t /\
     u + a <= c - &13 / &50 * t /\ v < t + &13 / &50 * c /\ t + &13 / &50 * c < v + a /\
     u < c - &4 / &5 * t /\ c - &4 / &5 * t < u + a /\ v + a <= t + &4 / &5 * c /\
     (forall y. &13 / &50 <= y ==> y <= &4 / &5 ==> ~linside c s u v a (&1) y)
     ==> c * (u + a) + t * (v + a) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  MP_TAC(SPECL [`--(u + a)`; `--u`; `--(v + a)`; `--v`; `--(c - &13 / &50 * t)`;
                `--(t + &13 / &50 * c)`; `--(c - &4 / &5 * t)`; `--(t + &4 / &5 * c)`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY C972NH_LIN THEN
    X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - w) * &13 / &50 + w * &4 / &5` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`&0 <= w`; `w <= &1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`&0 <= w`; `w <= &1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[linside; CONTRAPOS_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC);;

(* Lean: northwest_negative_half (private) *)
let C972NH_NEGATIVE_HALF = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&2 / &5) (&1) /\ linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1 / &2) (&0) /\
     ~linside c s u v a (--(&1 / &10)) (&3 / &5) /\
     (forall y. &13 / &50 <= y ==> y <= &4 / &5 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`] C972NH_RIGHT_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c * c + t * t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C972NH_UNFOLD_TAC THEN
  SUBGOAL_THEN `--t <= u` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    C972NH_OMIT_TAC `~linside c (--t) u v a (&0) (&1)`;
    ALL_TAC] THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `v + a <= t * (&1 / &2) + c` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    C972NH_OMIT_TAC `~linside c (--t) u v a (&1 / &2) (&1)`;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * (&1 / &2)` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    C972NH_OMIT_TAC `~linside c (--t) u v a (&1 / &2) (&0)`;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c / &2 + t` ASSUME_TAC THENL [C972NH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (t - (&1 - c / &2)) * (t + (&1 - c / &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN C972NH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c < &4 / &5` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    SUBGOAL_THEN `&0 <= c * (c - &4 / &5)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN C972NH_LIN; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < (t - (&1 - c / &2)) * (t + (&1 - c / &2))`; `c * c + t * t = &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &5 < t` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    SUBGOAL_THEN `&0 < (&4 / &5 - c) * (&4 / &5 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN C972NH_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t * (&3 / &5 - t)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN C972NH_LIN; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`t <= &3 / &5`; `c * c + t * t = &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v < t + &13 / &50 * c` ASSUME_TAC THENL [C972NH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `t + &13 / &50 * c < v + a` ASSUME_TAC THENL [C972NH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c - &13 / &50 * t` ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `&13 / &50` o check (is_forall o concl)) THEN
    C972NH_BANDS_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u < c - &4 / &5 * t` ASSUME_TAC THENL [C972NH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `v < t + &4 / &5 * c` ASSUME_TAC THENL [C972NH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `u < --(&1 / &10) * c - &3 / &5 * t` ASSUME_TAC THENL
   [ASM_CASES_TAC `c - &4 / &5 * t < u + a` THENL
     [SUBGOAL_THEN `v + a <= t + &4 / &5 * c` ASSUME_TAC THENL
       [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
        FIRST_ASSUM(MP_TAC o SPEC `&4 / &5` o check (is_forall o concl)) THEN
        C972NH_BANDS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `c * (u + a) + t * (v + a) <= &1` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (c - &7 / &10) * (&1 - c)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN C972NH_LIN; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (c - &7 / &10) * t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN C972NH_LIN; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < c * (a - &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN C972NH_LIN; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < t * (v + a - (&2 / &5 * t + c))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN C972NH_LIN; ALL_TAC] THEN
      SUBGOAL_THEN `c * u < c * (--(&1 / &10) * c - &3 / &5 * t)` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`c * (u + a) + t * (v + a) <= &1`; `&0 <= (c - &7 / &10) * (&1 - c)`;
          `&0 <= (c - &7 / &10) * t`; `&0 < c * (a - &1)`; `&0 < t * (v + a - (&2 / &5 * t + c))`;
          `c * c + t * t = &1`; `&7 / &10 < c`; `c <= &1`; `&3 / &5 < t`] THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
      C972NH_LIN];
    ALL_TAC] THEN
  C972NH_OMIT_TAC `~linside c (--t) u v a (--(&1 / &10)) (&3 / &5)`);;

(* the canonical frame of a local square: all linside facts restated for it *)
let C972NH_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C972NH_LIN; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `cr:real`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ar:real = a`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]);;

let C972NH_POS_TAC =
  MATCH_MP_TAC C972NH_POSITIVE_HALF THEN ASM_REWRITE_TAC[] THEN C972NH_LIN;;
let C972NH_NEG_TAC =
  MATCH_MP_TAC C972NH_NEGATIVE_HALF THEN EXISTS_TAC `--sr` THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN C972NH_LIN;;

(* Lean: northwest_half_local (private) *)
let C972NH_HALF_LOCAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&2 / &5) (&1) /\ linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\ ~linside c s u v a (&0) (&1) /\
     ~linside c s u v a (&1 / &2) (&0) /\ ~linside c s u v a (--(&1 / &10)) (&3 / &5) /\
     (forall y. &13 / &50 <= y ==> y <= &4 / &5 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NH_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= sr` THENL [C972NH_POS_TAC; C972NH_NEG_TAC]);;

(* Lean: northwest_half_or_vertical_local (private) *)
let C972NH_HALF_OR_VERTICAL_LOCAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&2 / &5) (&1) /\ linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1 / &2) (&0) /\
     (forall y. &13 / &50 <= y ==> y <= &4 / &5 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&1 / &2) (&1) \/
         (linside c s u v a (&0) (&2 / &5) /\ linside c s u v a (&0) (&31 / &50))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NH_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [DISJ2_TAC THEN C972NH_UNFOLD_TAC THEN REWRITE_TAC[linside] THEN C972NH_LIN;
    ASM_CASES_TAC `linside cr sr ur vr a (--(&1 / &10)) (&3 / &5)` THENL
     [DISJ2_TAC THEN C972NH_UNFOLD_TAC THEN REWRITE_TAC[linside] THEN C972NH_LIN;
      DISJ1_TAC THEN C972NH_NEG_TAC]]);;

(* side conditions of a local lemma at an owner tuple *)
let C972NH_SIDE_TAC =
  REWRITE_TAC[REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C972CS_CLASH_TAC;
         X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
         MP_TAC(SPECL (C972MC_V5 @ [`&2 + y`]) C972MC_LEFT_BAR) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN C972CS_CLASH_TAC;
         RASM_ARITH_TAC];;

let C972NH_NW = c972nh_tr22 (c972ur_px (c972nh_tuple 2048));;
let C972NH_PULL_TAC th =
  MP_TAC(SPECL C972NH_NW th) THEN
  REWRITE_TAC[C972NF_TRANSLATED] THEN REWRITE_TAC[LINSIDE_PULLX] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;

(* Lean: northwest_halfpoint_of_northeast_origin *)
let C972NH_NORTHWEST_HALFPOINT_OF_NORTHEAST_ORIGIN = prove
 (c972nh_stmt [c972nh_own 1024 `&2` `&3`] (c972nh_own 2048 `&3 / &2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_F7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_WEST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972NF_NORTHWEST_FORWARD) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C972CS_OWNER_TAC 1024 THEN C972CS_OWNER_TAC 2048 THEN
  SUBGOAL_THEN (c972nh_own 1024 `&21 / &10` `&13 / &5`) ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL (c972nh_tuple 1024) C972NF_NORTHEAST_UPPER_ANCHOR) THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC THEN C972CS_CLASH_TAC; RASM_ARITH_TAC];
    ALL_TAC] THEN
  C972NH_PULL_TAC C972NH_HALF_LOCAL THEN DISCH_THEN MATCH_MP_TAC THEN C972NH_SIDE_TAC);;

(* Lean: one_corner_of_northeast_origin *)
let C972NH_ONE_CORNER_OF_NORTHEAST_ORIGIN = prove
 (c972nh_stmt [c972nh_own 1024 `&2` `&3`] (c972nh_own 2 `&1` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPEC_ALL C972NH_NORTHWEST_HALFPOINT_OF_NORTHEAST_ORIGIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MP_TAC(SPEC_ALL C972MC_LEFT_MISSING_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: northwest_half_or_vertical *)
let C972NH_NORTHWEST_HALF_OR_VERTICAL = prove
 (c972nh_stmt [] (mk_disj(c972nh_own 2048 `&3 / &2` `&3`,
                          mk_conj(c972nh_own 2048 `&2` `&12 / &5`, c972nh_own 2048 `&2` `&131 / &50`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_WEST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972NF_NORTHWEST_FORWARD) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972NF_NORTHWEST_MISSING_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C972CS_OWNER_TAC 2048 THEN
  C972NH_PULL_TAC C972NH_HALF_OR_VERTICAL_LOCAL THEN DISCH_THEN MATCH_MP_TAC THEN C972NH_SIDE_TAC);;
