(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4UniformProfile.lean          *)
(* (N12Compact.Completion.OtherCases.C983).  One actual southeast profile    *)
(* for both northeast components.  Conventions of F4Filters / F4Origins      *)
(* (owners p 5 / 6 / 7 / 9 / 10 = owner 512 / 1024 / 2304 / 8192 / 16384;   *)
(* j IN actual p i is c983f4f_mem j i).  A Lean OpenSquare E is              *)
(* cE sE uE vE aE with its unit normal and positive side explicit (loU = uE);*)
(* q.translated 2 2 = (c, s, u - (c 2 + s 2), v - (--s 2 + c 2), a)          *)
(* (C983FUP_TRANSLATED).  F4BottomMidpoint.SoutheastData =                   *)
(* f4bm_southeast_data; F4BarAngle.bounds = C983FBA_BOUNDS;                  *)
(* F4SoutheastSign.exists_negative = C983FSG_EXISTS_NEGATIVE; seed_inside /  *)
(* auxiliary_inside / owners_apart = c983fo_facts / c983f4f_point;           *)
(* f4_southeast_g6 = C983F4OJ_F4_SOUTHEAST_G6, f4_southeast =                *)
(* C983F4F_F4_SOUTHEAST, f4_right_origin = C983FNT_F4_RIGHT_ORIGIN,          *)
(* f4_merged_center = C983FCE_F4_MERGED_CENTER, f4_northeast_sharp =         *)
(* C983FNT_F4_NORTHEAST_SHARP, bottom_bar = C983AB_BOTTOM_BAR.  Tag C983FUP_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4NortheastTransfer.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4SoutheastSign.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4BarAngle.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4BottomMidpoint.ml";;
needs "n12/geometry/CP_OtherCases_C983_ActualBars.ml";;

(* Lean: f4_uniform_negative_bounds *)
let C983FUP_F4_UNIFORM_NEGATIVE_BOUNDS = prove
 (`forall c s u v a t alpha beta.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 < t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&1) (--(&13 / &50)) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a alpha beta /\
     ~linside c s u v a (&1) (&0) /\
     (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside c s u v a x (--(&1))) /\
     ((alpha = &21 / &40 /\ beta = &1 / &8) \/ (alpha = &21 / &50 /\ beta = &4 / &25))
     ==> f4bm_southeast_data c s u v a t /\ t / (&1 + c) < &3 / &20 /\ &13 / &50 * t <= u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  MP_TAC (SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `t:real`; `alpha:real`; `beta:real`]
            C983FBA_BOUNDS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
           REWRITE_TAC[GSYM IMP_IMP] THEN FIRST_ASSUM ACCEPT_TAC;
           RASM_ARITH_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN `t < &3 / &20 * (&1 + c)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `t / (&1 + c) < &3 / &20`)) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &1 + c`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN UNDISCH_TAC `&0 < c` THEN
    REWRITE_TAC[REAL_NEG_MUL2] THEN REPEAT DISCH_TAC THEN
    NLIN_TAC [SPEC `t:real` REAL_LE_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN `t < &3 / &10` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&19 / &20 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_NEG_MUL2] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c * c <= (&19 / &20) * (&19 / &20) /\ t * t < (&3 / &10) * (&3 / &10)`
      MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN RASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL2 THEN RASM_ARITH_TAC];
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c (--t) u v a (&1) (&0)` THEN REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME)
      [`linside c (--t) u v a (&13 / &50) (&0)`; `linside c (--t) u v a (&1) (--(&13 / &50))`;
       `&0 < c`; `&0 < t`; `t < v + a`] THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[f4bm_southeast_data]);;

(* translated 2 2 *)
let C983FUP_TRANSLATED = prove
 (`forall c s u v a tx ty x y.
     linside c s (u - (c * tx + s * ty)) (v - (--s * tx + c * ty)) a x y <=>
     linside c s u v a (tx + x) (ty + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let c983fup_tr22 q = match q with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&2`) (mul s `&2`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&2`) (mul c `&2`)); a]
  | _ -> failwith "c983fup_tr22";;

let C983FUP_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let C983FUP_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C983FUP_RED = ASM_REWRITE_TAC[C983FUP_TRANSLATED] THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;

(* Lean: f4_southeast_profile *)
let C983FUP_F4_SOUTHEAST_PROFILE =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f4 = ASSUME (c983f4f_mem 4 7) in
  let use th = c983f4oj_use th [f4] in
  let inward = c983f4f_point f4 in
  let elbow = c983f4f_point (use C983F4OJ_F4_SOUTHEAST_G6) in
  let outer = c983f4f_point (use C983F4F_F4_SOUTHEAST) in
  let marker = seed 5 `&47 / &20` `&33 / &20` in
  let right = excl 512 16384 (use C983FNT_F4_RIGHT_ORIGIN) in
  let missf = excl 512 2304 inward in
  let center = use C983FCE_F4_MERGED_CENTER in
  let sharp = use C983FNT_F4_NORTHEAST_SHARP in
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
  let tW = c983fup_tr22 (c983ab_own 2304) and tS = c983fup_tr22 (c983ab_own 512) in
  let own512 x y = c983ab_in 512 x y in
  let goal = list_mk_exists(C983FUP_E @ [`t:real`],
    list_mk_conj [`cE * cE + sE * sE = &1`; `&0 < aE`; `aE:real = l`;
      list_mk_forall([`x:real`; `y:real`],
        mk_iff(list_mk_comb(`linside`, C983FUP_E @ [`x:real`; `y:real`]),
               own512 `x + &2` `y + &2`));
      list_mk_comb(`f4bm_southeast_data`, C983FUP_E @ [`t:real`]);
      `t / (&1 + cE) < &3 / &20`; `&13 / &50 * t <= uE`]) in
  let side_tac =
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           C983FUP_RED THEN ASM_REWRITE_TAC[] THEN NO_TAC;
           C983FUP_RED THEN X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
           MP_TAC (SPEC `&2 + x` bar) THEN
           ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
           ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
           MP_TAC (SPECL [`&2 + x`; `&1`] (apart 512 8192)) THEN ASM_REWRITE_TAC[];
           CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
           RASM_ARITH_TAC] in
  let case (alpha, beta) pt =
    MP_TAC (SPECL (C983FUP_C @ [`t:real`; alpha; beta]) C983FUP_F4_UNIFORM_NEGATIVE_BOUNDS) THEN
    ANTS_TAC THENL
     [ASSUME_TAC (excl 512 1024 pt) THEN REPEAT CONJ_TAC THEN side_tac; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC (C983FUP_C @ [`t:real`]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[C983FUP_TRANSLATED] THEN REWRITE_TAC[REAL_ADD_SYM] in
  prove
   (c983sa_stmt [c983f4f_mem 4 7] goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY ASSUME_TAC [side; pos; marker; elbow; outer; right; missf; inward; center;
                          seed 7 `&33 / &20` `&33 / &20`; seed 7 `&33 / &20` `&47 / &20`] THEN
    MP_TAC (SPECL (tW @ tS) C983FSG_EXISTS_NEGATIVE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [ACCEPT_TAC (unit 2304); ACCEPT_TAC (unit 512); FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
             REWRITE_TAC[ldisj; C983FUP_TRANSLATED] THEN REWRITE_TAC[apart 2304 512] THEN NO_TAC;
             C983FUP_RED THEN ASM_REWRITE_TAC[] THEN NO_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC (C983FUP_C @ [`t:real`]) THEN STRIP_TAC THEN
    DISJ_CASES_TAC sharp THENL
     [case (`&21 / &40`, `&1 / &8`) (ASSUME (lhand (concl sharp)));
      case (`&21 / &50`, `&4 / &25`) (ASSUME (rand (concl sharp)))]);;
