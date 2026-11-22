(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4Filters.lean.               *)
(* Literal local ownership implications for the C983 F4 entrance.           *)
(* actual p i = c983e_actual c1 c2 a b l i, originalComponents i = EL i      *)
(* c983e_original_components (Entrance); owners p i = owner at mask         *)
(* EL i c983ri_owner_code (2 -> 12, 5 -> 512, 6 -> 1024, 7 -> 2304,          *)
(* 9 -> 8192, 10 -> 16384).  Fin 12 indices are i < 12.                      *)
(* inward_outward_impossible = C983IOP_INWARD_OUTWARD_IMPOSSIBLE,            *)
(* bottom_bar = C983AB_BOTTOM_BAR.  Packing statements have hypotheses       *)
(* NPACK c1 c2 a b l /\ IMAGE binarysum (FFP ..) = c983ri_family /\ ...      *)
(* (Lean p, hf, ...).  Tag C983F4F_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_ActualBars.ml";;
needs "n12/geometry/CP_OtherCases_C983_InwardOutwardPair.ml";;

let C983F4F_NP = `NPACK c1 c2 a b l` and C983F4F_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family`;;
let c983f4f_hh () = CONJ (ASSUME C983F4F_NP) (ASSUME C983F4F_IMG);;
let c983f4f_lt i = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral i) `12`));;
let c983f4f_act m = mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(`c983e_actual`, `c1:num->real`),
                      `c2:num->real`), `a:num->real`), `b:num->real`), `l:real`), mk_small_numeral m);;
let c983f4f_mem j i = mk_binop `(IN):num->(num->bool)->bool` (mk_small_numeral j) (c983f4f_act i);;
let C983F4F_ACT_CONV = REWRITE_CONV[c983e_actual; c983ri_owner_code] THENC ONCE_DEPTH_CONV EL_CONV;;
(* prove a packing statement  !c1 c2 a b l. A1 /\ .. ==> C  from th with hypotheses among the Ai
   (NPACK and IMAGE separately) *)
let c983f4f_close stmt th = prove(stmt, REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN ACCEPT_TAC th);;
let c983f4f_check_tac =
  REWRITE_TAC[c983e_original_components] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[MEM] THEN GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;
(* |- MEM (actual i) (originalComponents i)  (hyps NPACK, IMAGE) *)
let c983f4f_orig i =
  MP (SPECL (C983E_VARS @ [mk_small_numeral i]) C983E_ORIGINAL_ACTUAL_MEM)
     (CONJ (ASSUME C983F4F_NP) (CONJ (ASSUME C983F4F_IMG) (c983f4f_lt i)));;

(* Lean: absent_of_foreign *)
let C983F4F_ABSENT_OF_FOREIGN = prove
 (`forall c1 c2 a b l i j point. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     i < 12 /\ j < 12 /\ ~(i = j) /\ point IN c983e_actual c1 c2 a b l i
     ==> ~(point IN c983e_actual c1 c2 a b l j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`; `j:num`]
           C983E_ACTUAL_DISJOINT) THEN
  ASM_REWRITE_TAC[IN_DISJOINT] THEN ASM_MESON_TAC[]);;

(* forward form at literal indices: from |- point IN actual i  to  |- ~(point IN actual j) *)
let c983f4f_absent i j th =
  let pt = lhand (concl th) in
  let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral i, mk_small_numeral j))) in
  MP (SPECL (C983E_VARS @ [mk_small_numeral i; mk_small_numeral j; pt]) C983F4F_ABSENT_OF_FOREIGN)
     (end_itlist CONJ [ASSUME C983F4F_NP; ASSUME C983F4F_IMG; c983f4f_lt i; c983f4f_lt j; ne; th]);;

(* Lean: point_exact *)
let C983F4F_POINT_EXACT = prove
 (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`; `point:num`],
   mk_imp(`point < 20`,
     mk_eq(list_mk_comb(`linside`, c983e_own `i:num` @ [`EL point (AUXPTS 2)$1`; `EL point (AUXPTS 2)$2`]),
           `point IN c983e_actual c1 c2 a b l i`)))),
  REWRITE_TAC[c983e_actual] THEN SIMP_TAC[OO_AUX_EXACT]);;

(* the literal point of a membership:  |- j IN actual i  to  |- linside (owner i) x_j y_j *)
let c983f4f_point th =
  let j = dest_small_numeral (lhand (concl th)) in
  CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (c983ab_point j (CONV_RULE C983F4F_ACT_CONV th));;

(* Lean: merged_check (private) *)
let C983F4F_MERGED_CHECK = prove
 (`forall s. MEM s (EL 7 c983e_original_components) ==> 13 IN s`, c983f4f_check_tac);;

(* Lean: merged_g3 *)
let C983F4F_MERGED_G3 =
  let th = MATCH_MP C983F4F_MERGED_CHECK (c983f4f_orig 7) in
  c983f4f_close `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family
                   ==> 13 IN c983e_actual c1 c2 a b l 7` th;;

(* Lean: southeast_f4_check (private) *)
let C983F4F_SOUTHEAST_F4_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(4 IN s) ==> 8 IN s`, c983f4f_check_tac);;

let c983f4f_southeast () =
  let f4 = ASSUME (c983f4f_mem 4 7) in
  MP (MATCH_MP C983F4F_SOUTHEAST_F4_CHECK (c983f4f_orig 5)) (c983f4f_absent 7 5 f4);;

(* Lean: f4_southeast *)
let C983F4F_F4_SOUTHEAST = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7 ==> 8 IN c983e_actual c1 c2 a b l 5` (c983f4f_southeast ());;

(* Lean: right_from_f8_check (private) *)
let C983F4F_RIGHT_FROM_F8_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(8 IN s) ==> 9 IN s /\ 19 IN s`, c983f4f_check_tac);;

let c983f4f_right () =
  MP (MATCH_MP C983F4F_RIGHT_FROM_F8_CHECK (c983f4f_orig 10)) (c983f4f_absent 5 10 (c983f4f_southeast ()));;

(* Lean: f4_right *)
let C983F4F_F4_RIGHT = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7
     ==> 9 IN c983e_actual c1 c2 a b l 10 /\ 19 IN c983e_actual c1 c2 a b l 10` (c983f4f_right ());;

(* Lean: northeast_f4_check (private) *)
let C983F4F_NORTHEAST_F4_CHECK = prove
 (`forall s. MEM s (EL 6 c983e_original_components) ==>
       ~(4 IN s) ==> ~(8 IN s) ==> ~(9 IN s) ==> ~(13 IN s) ==> ~(19 IN s) ==>
       (5 IN s \/ 7 IN s) /\ (16 IN s \/ 17 IN s)`, c983f4f_check_tac);;

let c983f4f_northeast () =
  let r = c983f4f_right () in
  let g3 = MATCH_MP C983F4F_MERGED_CHECK (c983f4f_orig 7) in
  itlist (fun a th -> MP th a)
    (rev [c983f4f_absent 7 6 (ASSUME (c983f4f_mem 4 7)); c983f4f_absent 5 6 (c983f4f_southeast ());
          c983f4f_absent 10 6 (CONJUNCT1 r); c983f4f_absent 7 6 g3; c983f4f_absent 10 6 (CONJUNCT2 r)])
    (MATCH_MP C983F4F_NORTHEAST_F4_CHECK (c983f4f_orig 6));;

(* Lean: f4_northeast *)
let C983F4F_F4_NORTHEAST = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7
     ==> (5 IN c983e_actual c1 c2 a b l 6 \/ 7 IN c983e_actual c1 c2 a b l 6) /\
         (16 IN c983e_actual c1 c2 a b l 6 \/ 17 IN c983e_actual c1 c2 a b l 6)` (c983f4f_northeast ());;

(* Lean: southeast_outward_check (private) *)
let C983F4F_SOUTHEAST_OUTWARD_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==>
       ~(4 IN s) ==> ~(9 IN s) ==> ~(5 IN s) ==> ~(16 IN s) ==> 8 IN s ==> s = {8, 18}`,
  c983f4f_check_tac);;

let c983f4f_outward () =
  itlist (fun a th -> MP th a)
    (rev [c983f4f_absent 7 5 (ASSUME (c983f4f_mem 4 7)); c983f4f_absent 10 5 (CONJUNCT1 (c983f4f_right ()));
          c983f4f_absent 6 5 (ASSUME (c983f4f_mem 5 6)); c983f4f_absent 6 5 (ASSUME (c983f4f_mem 16 6));
          c983f4f_southeast ()])
    (MATCH_MP C983F4F_SOUTHEAST_OUTWARD_CHECK (c983f4f_orig 5));;

(* Lean: f4_inward_forces_outward *)
let C983F4F_F4_INWARD_FORCES_OUTWARD = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7 /\ 5 IN c983e_actual c1 c2 a b l 6 /\ 16 IN c983e_actual c1 c2 a b l 6
     ==> c983e_actual c1 c2 a b l 5 = {8, 18}` (c983f4f_outward ());;

let c983f4f_exclusion () =
  let outward = c983f4f_outward () in
  let memo j = EQT_ELIM (REWRITE_CONV[outward; IN_INSERT; NOT_IN_EMPTY] (c983f4f_mem j 5)) in
  let np = ASSUME C983F4F_NP in
  let unit m = MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let side = MP (SPECL C983E_VARS OO_SIDE) np in
  let pos = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  let hh = c983f4f_hh () in
  let seed i x y = MP (SPECL C983E_VARS (c983e_seed_inside i (x, y))) hh in
  let apart m n = MP (SPECL C983E_VARS (oo_apart C983E_F m n)) hh in
  let missing =
    let eq = SPECL (C983E_VARS @ [`1024`]) (oo_aux_point 7) in
    let nm = CONV_RULE C983F4F_ACT_CONV (ASSUME (mk_neg (c983f4f_mem 7 6))) in
    CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (EQ_MP (SYM (AP_TERM `(~)` eq)) nm) in
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) hh in
  let facts = [unit 1024; unit 512; unit 8192; unit 12; unit 16384; unit 2304; pos; side; REFL `l:real`;
               seed 6 `&47 / &20` `&47 / &20`;
               c983f4f_point (ASSUME (c983f4f_mem 5 6)); c983f4f_point (ASSUME (c983f4f_mem 16 6));
               missing; seed 5 `&47 / &20` `&33 / &20`; c983f4f_point (memo 8); c983f4f_point (memo 18);
               seed 7 `&33 / &20` `&47 / &20`; seed 10 `&1543 / &500` `&2`;
               seed 2 `&3` `&1`; seed 2 `&1543 / &500` `&1`; bar;
               apart 1024 512; apart 1024 2304; apart 512 16384; apart 512 12; apart 512 8192] in
  let own m = c983ab_own m in
  let spec = SPECL (own 1024 @ own 512 @ own 8192 @ own 12 @ own 16384 @ own 2304)
                   C983IOP_INWARD_OUTWARD_IMPOSSIBLE in
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm = try find (fun f -> aconv (concl f) tm) facts
              with Failure _ -> failwith ("c983f4f_exclusion: " ^ string_of_term tm) in
  MP spec (end_itlist CONJ (map pa ants));;

(* Lean: f4_inward_outward_exclusion *)
let C983F4F_F4_INWARD_OUTWARD_EXCLUSION = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7 /\ 5 IN c983e_actual c1 c2 a b l 6 /\ 16 IN c983e_actual c1 c2 a b l 6 /\
     ~(7 IN c983e_actual c1 c2 a b l 6) ==> false` (c983f4f_exclusion ());;

(* Lean: top_f7_check (private) *)
let C983F4F_TOP_F7_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> 7 IN s ==> 17 IN s`, c983f4f_check_tac);;

let c983f4f_top_avoids () =
  let topF7 = ASSUME (c983f4f_mem 7 11) in
  let topG7 = MP (MATCH_MP C983F4F_TOP_F7_CHECK (c983f4f_orig 11)) topF7 in
  let noF7 = c983f4f_absent 11 6 topF7 and noG7 = c983f4f_absent 11 6 topG7 in
  let cover = c983f4f_northeast () in
  let res d n = DISJ_CASES d (ASSUME (lhand (concl d))) (CONTR (lhand (concl d)) (MP (NOT_ELIM n) (ASSUME (rand (concl d))))) in
  let f5 = res (CONJUNCT1 cover) noF7 and g6 = res (CONJUNCT2 cover) noG7 in
  let ex = c983f4f_exclusion () in
  let ex = PROVE_HYP f5 (PROVE_HYP g6 (PROVE_HYP noF7 ex)) in
  NOT_INTRO (DISCH (c983f4f_mem 7 11) ex);;

(* Lean: f4_top_avoids_f7 *)
let C983F4F_F4_TOP_AVOIDS_F7 = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7 ==> ~(7 IN c983e_actual c1 c2 a b l 11)` (c983f4f_top_avoids ());;

(* Lean: top_f4_check (private) *)
let C983F4F_TOP_F4_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(7 IN s) ==> 3 IN s /\ 14 IN s`, c983f4f_check_tac);;

(* Lean: f4_top *)
let C983F4F_F4_TOP = c983f4f_close
  `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family /\
     4 IN c983e_actual c1 c2 a b l 7
     ==> 3 IN c983e_actual c1 c2 a b l 11 /\ 14 IN c983e_actual c1 c2 a b l 11`
  (MP (MATCH_MP C983F4F_TOP_F4_CHECK (c983f4f_orig 11)) (c983f4f_top_avoids ()));;
