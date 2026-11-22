(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F5RightFinal.lean.             *)
(* Deletion of every F5 right component containing both right auxiliaries, *)
(* and the final F5 central components.  Conventions of                      *)
(* CP_OtherCases_C983_F4Filters.ml / F5Filters.ml: owners p 5 / 7 / 9 / 10 = *)
(* owner 512 / 2304 / 8192 / 16384, actual p i = c983e_actual .. i;          *)
(* q.translated 2 2 is the tuple c s (u - (c * &2 + s * &2))                 *)
(* (v - (--s * &2 + c * &2)) a (C983AOP_TRANSLATE).                          *)
(* InwardTwoBars.impossible = OCITB_IMPOSSIBLE, f5_merged_center =           *)
(* C983MCF_F5_MERGED_CENTER, f5_southeast_g6 / f5_southeast_components /     *)
(* f5_right_components / f5_upper_of_right_g9 = C983F5_*, f5_right_not_lower *)
(* = C983F5LR_F5_RIGHT_NOT_LOWER, bottom_bar = C983AB_BOTTOM_BAR,            *)
(* vertical_segment = OO_VERTICAL_SEGMENT.  Tag C983F5RF_.                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5LowerRight.ml";;
needs "n12/geometry/CP_OtherCases_InwardTwoBars.ml";;
needs "n12/geometry/CP_OtherCases_C983_ActualOutwardPair.ml";;

(* Lean: southeast_without_f8_check (private) *)
let C983F5RF_SOUTHEAST_WITHOUT_F8_CHECK = prove
 (`forall s. MEM s c983f5_southeast_components ==> ~(8 IN s) ==> 4 IN s`,
  c983f5_check [c983f5_southeast_components]);;

(* the two foreign bars, read through the translation by (2, 2) *)
let C983F5RF_BOTTOM_BAR_TRANSLATED = prove
 (`forall c s u v a. (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a z (&1))
     ==> forall x. &13 / &50 <= x ==> x <= &4 / &5
             ==> ~linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a x (--(&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C983AOP_TRANSLATE; REAL_ARITH `--(&1) + &2 = &1`] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + &2`) THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REWRITE_TAC[]);;

let C983F5RF_RIGHT_BAR_TRANSLATED = prove
 (`forall c s u v a. (forall z. &87 / &50 <= z ==> z <= &113 / &50 ==> ~linside c s u v a (&3) z)
     ==> forall y. --(&13 / &50) <= y ==> y <= &0
             ==> ~linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a (&1) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C983AOP_TRANSLATE; REAL_ARITH `&1 + &2 = &3`] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y + &2`) THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REWRITE_TAC[]);;

let c983f5rf_trans m =
  let [c; s; u; v; a] = c983ab_own m in
  let sub x y = mk_binop `(-):real->real->real` x y and add x y = mk_binop `(+):real->real->real` x y
  and mul x y = mk_binop `( * ):real->real->real` x y and neg x = mk_comb(`(--):real->real`, x) in
  [c; s; sub u (add (mul c `&2`) (mul s `&2`)); sub v (add (mul (neg s) `&2`) (mul c `&2`)); a];;

let C983F5RF_CONV = REWRITE_CONV[C983AOP_TRANSLATE] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* Lean: f5_right_not_both *)
let c983f5rf_not_both f5 rF8 rF9 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let eF4 = MP (MATCH_MP C983F5RF_SOUTHEAST_WITHOUT_F8_CHECK (c983f5_use C983F5_F5_SOUTHEAST_COMPONENTS [f5]))
               (c983f4f_absent 10 5 rF8) in
  let elbow = c983f5_use C983F5_F5_SOUTHEAST_G6 [f5] in
  let rLower = c983f4f_point rF8 and rUpper = c983f4f_point rF9 in
  let bottom = MP (SPECL (c983ab_own 512) C983F5RF_BOTTOM_BAR_TRANSLATED) (c983sa_bar_excl 512) in
  let right =
    let lo = `&87 / &50 <= z` and hi = `z <= &113 / &50` in
    let seg = MP (SPECL (c983ab_own 16384 @ [`&3`; `&87 / &50`; `&113 / &50`; `z:real`]) OO_VERTICAL_SEGMENT)
                 (end_itlist CONJ [rLower; rUpper; EQT_ELIM (REAL_RAT_REDUCE_CONV `&87 / &50 < &113 / &50`);
                                   ASSUME lo; ASSUME hi]) in
    MP (SPECL (c983ab_own 512) C983F5RF_RIGHT_BAR_TRANSLATED)
       (GEN `z:real` (DISCH lo (DISCH hi (excl 512 16384 seg)))) in
  let disj =
    let tm = list_mk_comb(`ldisj`, c983f5rf_trans 2304 @ c983f5rf_trans 512) in
    let d = MP (SPECL C983E_VARS (oo_apart C983E_F 2304 512)) (c983f4f_hh ()) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; C983AOP_TRANSLATE] tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`x + &2`; `y + &2`] (REWRITE_RULE[ldisj] d)))) in
  let facts = [unit 2304; unit 512; pos; side; seed 7 `&33 / &20` `&33 / &20`;
               c983f5_use C983MCF_F5_MERGED_CENTER [f5]; c983f4f_point f5;
               seed 5 `&47 / &20` `&33 / &20`; c983f4f_point eF4; c983f4f_point elbow;
               bottom; right; disj] in
  c983sa_apply C983F5RF_CONV (SPECL (c983f5rf_trans 2304 @ c983f5rf_trans 512) OCITB_IMPOSSIBLE) facts;;

let C983F5RF_F5_RIGHT_NOT_BOTH =
  let both = mk_conj(c983f4f_mem 8 10, c983f4f_mem 9 10) in
  let b = ASSUME both in
  let f = c983f5rf_not_both (c983f5_f5 ()) (CONJUNCT1 b) (CONJUNCT2 b) in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (mk_neg both)) (NOT_INTRO (DISCH both f));;

(* Lean: right_final_check (private) *)
let C983F5RF_RIGHT_FINAL_CHECK = prove
 (`forall s. MEM s c983f5_right_components ==> ~(s = {8, 18}) ==> ~(8 IN s /\ 9 IN s) ==> s = {9, 19}`,
  c983f5_check [c983f5_right_components]);;

(* Lean: f5_right_final *)
let c983f5rf_right_final f5 =
  c983f5_mps (MATCH_MP C983F5RF_RIGHT_FINAL_CHECK (c983f5_use C983F5_F5_RIGHT_COMPONENTS [f5]))
    [c983f5_use C983F5LR_F5_RIGHT_NOT_LOWER [f5]; c983f5_use C983F5RF_F5_RIGHT_NOT_BOTH [f5]];;
let C983F5RF_F5_RIGHT_FINAL = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] (mk_eq(c983f4f_act 10, `{9, 19}`))) (c983f5rf_right_final (c983f5_f5 ()));;

(* Lean: f5FinalSoutheast *)
let c983f5rf_final_southeast = new_definition
 `c983f5rf_final_southeast : (num->bool)list =
    [{4, 16}; {4, 16, 18}; {8, 16}; {8, 16, 18}; {4, 8, 16}; {4, 8, 16, 18}]`;;

(* Lean: southeast_final_check (private) *)
let C983F5RF_SOUTHEAST_FINAL_CHECK = prove
 (`forall s. MEM s c983f5_southeast_components ==> ~(9 IN s) ==> MEM s c983f5rf_final_southeast`,
  c983f5_check [c983f5_southeast_components; c983f5rf_final_southeast]);;

(* Lean: f5_final_central *)
let C983F5RF_F5_FINAL_CENTRAL =
  let f5 = c983f5_f5 () in
  let right = c983f5rf_right_final f5 in
  let memo j = EQT_ELIM ((REWRITE_CONV[right; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) (c983f4f_mem j 10)) in
  let rF9 = memo 9 and rG9 = memo 19 in
  let upper = c983f5_use C983F5_F5_UPPER_OF_RIGHT_G9 [f5; rG9] in
  let se = MP (MATCH_MP C983F5RF_SOUTHEAST_FINAL_CHECK (c983f5_use C983F5_F5_SOUTHEAST_COMPONENTS [f5]))
              (c983f4f_absent 10 5 rF9) in
  c983f4f_close
    (c983sa_stmt [c983f4f_mem 5 7]
      (list_mk_conj [c983f5_act_mem 5 `c983f5rf_final_southeast`; mk_eq(c983f4f_act 6, `{7, 17}`);
                     mk_eq(c983f4f_act 10, `{9, 19}`); mk_eq(c983f4f_act 11, `{3, 14}`)]))
    (end_itlist CONJ [se; CONJUNCT1 upper; right; CONJUNCT2 upper]);;
