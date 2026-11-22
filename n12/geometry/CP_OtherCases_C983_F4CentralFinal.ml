(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4CentralFinal.lean.          *)
(* Complete actual central and peripheral reduction in the C983 F4 branch.  *)
(* Conventions of CP_OtherCases_C983_F4Filters.ml / F5Filters.ml (owners p 5 *)
(* / 6 / 7 / 9 / 11 = owner 512 / 1024 / 2304 / 8192 / 32768; actual p i =   *)
(* c983e_actual c1 c2 a b l i).  F4PointTransfers.horizontal_original /      *)
(* upper_original = OCF4PT_HORIZONTAL_ORIGINAL / OCF4PT_UPPER_ORIGINAL,      *)
(* ElbowPoint.points_original = OCEP_POINTS_ORIGINAL, f4_southeast /         *)
(* f4_right / f4_top / merged_g3 = C983F4F_*, f4_southeast_g6 =              *)
(* C983F4OJ_F4_SOUTHEAST_G6, f4_northeast_g7 = C983F4CE_F4_NORTHEAST_G7,     *)
(* northeast_upper_point = C983SA_NORTHEAST_UPPER_POINT, f4_top_origin /     *)
(* f4_right_bar = C983FO_F4_TOP_ORIGIN / C983FO_F4_RIGHT_BAR, bottom_bar =   *)
(* C983AB_BOTTOM_BAR.  Tag C983F4CF_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4OutwardJoin.ml";;
needs "n12/geometry/CP_OtherCases_F4PointTransfers.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;

let c983f4cf_f4 () = ASSUME (c983f4f_mem 4 7);;
let c983f4cf_stmt concl = c983sa_stmt [c983f4f_mem 4 7] concl;;
let c983f4cf_memo ex j i =
  EQT_ELIM ((REWRITE_CONV[ex; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) (c983f4f_mem j i));;
let c983f4cf_bar52 () =
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
  let th = SPEC `&5 / &2` bar in
  MP (MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th)))))
     (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (rand (concl th)))));;

(* Lean: f4_southeast_crosspoint *)
let c983f4cf_southeast_crosspoint f4 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  c983sa_apply ALL_CONV (SPECL (c983ab_own 512) OCF4PT_HORIZONTAL_ORIGINAL)
    [unit 512; pos; side; seed 5 `&47 / &20` `&33 / &20`;
     c983f4f_point (c983f5_use C983F4OJ_F4_SOUTHEAST_G6 [f4]);
     c983f4f_point (c983f5_use C983F4F_F4_SOUTHEAST [f4]);
     excl 512 2304 (c983f4f_point f4); excl 512 8192 (c983f4cf_bar52 ())];;
let C983F4CF_F4_SOUTHEAST_CROSSPOINT = c983f4f_close (c983f4cf_stmt (c983ab_in 512 `&5 / &2` `&2`))
  (c983f4cf_southeast_crosspoint (c983f4cf_f4 ()));;

(* Lean: northeast_candidates_check (private) *)
let C983F4CF_NORTHEAST_CANDIDATES_CHECK = prove
 (`forall s. MEM s (EL 6 c983e_original_components) ==>
       ~(4 IN s) ==> ~(13 IN s) ==> ~(8 IN s) ==> ~(9 IN s) ==> ~(19 IN s) ==> ~(16 IN s) ==>
       ~(3 IN s) ==> ~(14 IN s) ==> s = {5, 17} \/ s = {7, 17} \/ s = {5, 7, 17}`,
  c983f4f_check_tac);;

(* Lean: f4_northeast_candidates *)
let c983f4cf_candidates f4 =
  let top = c983f5_use C983F4F_F4_TOP [f4] and right = c983f5_use C983F4F_F4_RIGHT [f4] in
  c983f5_mps (MATCH_MP C983F4CF_NORTHEAST_CANDIDATES_CHECK (c983f4f_orig 6))
    [c983f4f_absent 7 6 f4; c983f4f_absent 7 6 (c983f5_use C983F4F_MERGED_G3 []);
     c983f4f_absent 5 6 (c983f5_use C983F4F_F4_SOUTHEAST [f4]);
     c983f4f_absent 10 6 (CONJUNCT1 right); c983f4f_absent 10 6 (CONJUNCT2 right);
     c983f4f_absent 5 6 (c983f5_use C983F4OJ_F4_SOUTHEAST_G6 [f4]);
     c983f4f_absent 11 6 (CONJUNCT1 top); c983f4f_absent 11 6 (CONJUNCT2 top)];;
let c983f4cf_act6 s = mk_eq(c983f4f_act 6, s);;
let C983F4CF_F4_NORTHEAST_CANDIDATES = c983f4f_close
  (c983f4cf_stmt (list_mk_disj [c983f4cf_act6 `{5, 17}`; c983f4cf_act6 `{7, 17}`; c983f4cf_act6 `{5, 7, 17}`]))
  (c983f4cf_candidates (c983f4cf_f4 ()));;

(* Lean: f4_northeast_f7 *)
let c983f4cf_northeast_f7 f4 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let goal = c983f4f_mem 7 6 in
  let noF7 = ASSUME (mk_neg goal) in
  let cand = c983f4cf_candidates f4 in
  let d1, rest = dest_disj (concl cand) in
  let d2, d3 = dest_disj rest in
  let f5tm = c983f4f_mem 5 6 in
  let contra d = CONTR f5tm (MP (NOT_ELIM noF7) (c983f4cf_memo (ASSUME d) 7 6)) in
  let f5 = DISJ_CASES cand (c983f4cf_memo (ASSUME d1) 5 6)
             (DISJ_CASES (ASSUME rest) (contra d2) (contra d3)) in
  let t = c983sa_swx 1024 in
  let pts = c983sa_apply C983SA_SWX_CONV (SPECL t OCEP_POINTS_ORIGINAL)
    [MP (prove(mk_imp(concl (unit 1024), mk_eq(mk_binop `(+):real->real->real`
           (mk_binop `( * ):real->real->real` (hd t) (hd t)) (mk_binop `( * ):real->real->real` (el 1 t) (el 1 t)), `&1`)),
           CONV_TAC REAL_RING)) (unit 1024); side;
     seed 6 `&47 / &20` `&47 / &20`; c983f4f_point f5;
     c983f4f_point (c983f5_use C983F4CE_F4_NORTHEAST_G7 [f4]);
     excl 1024 2304 (seed 7 `&33 / &20` `&47 / &20`);
     PROVE_HYP noF7 (c983sa_missing 7 6);
     excl 1024 32768 (seed 11 `&2` `&1543 / &500`)] in
  let f = MP (NOT_ELIM (SPECL [`&5 / &2`; `&2`] (apart 512 1024)))
             (CONJ (c983f4cf_southeast_crosspoint f4) (CONJUNCT1 pts)) in
  CCONTR goal f;;
let C983F4CF_F4_NORTHEAST_F7 = c983f4f_close (c983f4cf_stmt (c983f4f_mem 7 6))
  (c983f4cf_northeast_f7 (c983f4cf_f4 ()));;

(* Lean: f4_southeast_avoids_f5 *)
let c983f4cf_avoids_f5 f4 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let sF5 = ASSUME (c983f4f_mem 5 5) in
  let lowerPoint = c983sa_apply ALL_CONV (SPECL (c983ab_own 512) OCF4PT_UPPER_ORIGINAL)
    [unit 512; pos; side; seed 5 `&47 / &20` `&33 / &20`;
     c983f4f_point (c983f5_use C983F4OJ_F4_SOUTHEAST_G6 [f4]);
     c983f4f_point (c983f5_use C983F4F_F4_SOUTHEAST [f4]); c983f4f_point sF5;
     excl 512 2304 (c983f4f_point f4)] in
  let upperPoint = c983f5_use C983SA_NORTHEAST_UPPER_POINT
    [c983f4cf_northeast_f7 f4; c983f4f_absent 5 6 sF5;
     c983f5_use C983FO_F4_TOP_ORIGIN [f4]; c983f5_use C983FO_F4_RIGHT_BAR [f4]] in
  let f = MP (NOT_ELIM (SPECL [`&101 / &40`; `&17 / &8`] (apart 512 1024))) (CONJ lowerPoint upperPoint) in
  NOT_INTRO (DISCH (c983f4f_mem 5 5) f);;
let C983F4CF_F4_SOUTHEAST_AVOIDS_F5 = c983f4f_close (c983f4cf_stmt (mk_neg (c983f4f_mem 5 5)))
  (c983f4cf_avoids_f5 (c983f4cf_f4 ()));;

(* Lean: southeast_final_check (private) *)
let C983F4CF_SOUTHEAST_FINAL_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==>
       ~(4 IN s) ==> ~(9 IN s) ==> ~(5 IN s) ==> 8 IN s ==> 16 IN s ==> s = {8, 16} \/ s = {8, 16, 18}`,
  c983f4f_check_tac);;

(* Lean: f4_southeast_final *)
let C983F4CF_F4_SOUTHEAST_FINAL =
  let f4 = c983f4cf_f4 () in
  c983f4f_close
   (c983f4cf_stmt (mk_disj(mk_eq(c983f4f_act 5, `{8, 16}`), mk_eq(c983f4f_act 5, `{8, 16, 18}`))))
   (c983f5_mps (MATCH_MP C983F4CF_SOUTHEAST_FINAL_CHECK (c983f4f_orig 5))
     [c983f4f_absent 7 5 f4; c983f4f_absent 10 5 (CONJUNCT1 (c983f5_use C983F4F_F4_RIGHT [f4]));
      c983f4cf_avoids_f5 f4; c983f5_use C983F4F_F4_SOUTHEAST [f4];
      c983f5_use C983F4OJ_F4_SOUTHEAST_G6 [f4]]);;

(* Lean: f4_northeast_final *)
let C983F4CF_F4_NORTHEAST_FINAL =
  let f4 = c983f4cf_f4 () in
  let cand = c983f4cf_candidates f4 in
  let d1, rest = dest_disj (concl cand) in
  let member = c983f4cf_northeast_f7 f4 in
  let bad = EQF_ELIM ((REWRITE_CONV[ASSUME d1; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) (concl member)) in
  c983f4f_close (c983f4cf_stmt rest)
    (DISJ_CASES cand (CONTR rest (MP (NOT_ELIM bad) member)) (ASSUME rest));;

(* Lean: right_final_check (private) *)
let C983F4CF_RIGHT_FINAL_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(8 IN s) ==> ~(16 IN s) ==> ~(7 IN s) ==> s = {9, 19}`,
  c983f4f_check_tac);;

(* Lean: f4_right_final *)
let C983F4CF_F4_RIGHT_FINAL =
  let f4 = c983f4cf_f4 () in
  c983f4f_close (c983f4cf_stmt (mk_eq(c983f4f_act 10, `{9, 19}`)))
   (c983f5_mps (MATCH_MP C983F4CF_RIGHT_FINAL_CHECK (c983f4f_orig 10))
     [c983f4f_absent 5 10 (c983f5_use C983F4F_F4_SOUTHEAST [f4]);
      c983f4f_absent 5 10 (c983f5_use C983F4OJ_F4_SOUTHEAST_G6 [f4]);
      c983f4f_absent 6 10 (c983f4cf_northeast_f7 f4)]);;
