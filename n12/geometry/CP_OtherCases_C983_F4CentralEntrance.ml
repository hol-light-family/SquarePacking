(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4CentralEntrance.lean.       *)
(* The F4 central entrance through the exact top owner.  Conventions of      *)
(* CP_OtherCases_C983_F5Filters.ml (owners p 3 -> 48, 5 -> 512, 6 -> 1024,   *)
(* 10 -> 16384, 11 -> 32768).  C981CompletionUpperPoint.point = C981UP_POINT, *)
(* OriginalOwners.vertical_segment = OO_VERTICAL_SEGMENT, f4_* of F4Filters /*)
(* F4Origins = C983F4F_F4_* / C983FO_F4_*.  Tag C983F4CE_.                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5Filters.ml";;
needs "n12/geometry/CP_C981_UpperPoint.ml";;

let c983f4ce_f4 () = ASSUME (c983f4f_mem 4 7);;
let c983f4ce_apart_at m n (x, y) pm pn =
  let ap = REWRITE_RULE[ldisj] (MP (SPECL C983E_VARS (oo_apart C983E_F m n)) (c983f4f_hh ())) in
  MP (NOT_ELIM (SPECL [x; y] ap)) (CONJ pm pn);;

let c983f4ce_g7 () =
  let f4 = c983f4ce_f4 () in
  let noG7 = ASSUME (mk_neg (c983f4f_mem 17 6)) in
  let cover = c983f5_use C983F4F_F4_NORTHEAST [f4] in
  let g6 = c983f5_res_right (CONJUNCT2 cover) noG7 in
  let f5 = ASSUME (c983f4f_mem 5 6) and nf5 = ASSUME (mk_neg (c983f4f_mem 5 6)) in
  let f7 = ASSUME (c983f4f_mem 7 6) and nf7 = ASSUME (mk_neg (c983f4f_mem 7 6)) in
  let case_f7 =
    let outward = c983f5_use C983F4F_F4_INWARD_FORCES_OUTWARD [f4; f5; g6] in
    let eG8 = EQT_ELIM ((REWRITE_CONV[outward; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV)
                          (c983f4f_mem 18 5)) in
    let eNoG6 = c983f4f_absent 6 5 g6 in
    let lower = c983f5_use C983SA_SOUTHEAST_OUTWARD_POINT
                  [c983f5_use C983F4F_F4_SOUTHEAST [f4]; eG8; eNoG6] in
    let upper = c983f5_use C983SA_NORTHEAST_INWARD_TOP_POINT [f5; g6; f7; noG7] in
    c983f4ce_apart_at 512 1024 (`&101 / &40`, `&17 / &8`) lower upper in
  let case_nf7 = c983f5_use C983F4F_F4_INWARD_OUTWARD_EXCLUSION [f4; f5; g6; nf7] in
  let case_f5 = DISJ_CASES (SPEC (c983f4f_mem 7 6) EXCLUDED_MIDDLE) case_f7 case_nf7 in
  let case_nf5 =
    let f7' = c983f5_res_left (CONJUNCT1 cover) nf5 in
    let right = c983f5_use C983F4F_F4_RIGHT [f4] in
    c983f5_use C983SA_NORTHEAST_MIXED_EXCLUSION [g6; f7'; nf5; noG7; CONJUNCT1 right; CONJUNCT2 right] in
  CCONTR (c983f4f_mem 17 6) (DISJ_CASES (SPEC (c983f4f_mem 5 6) EXCLUDED_MIDDLE) case_f5 case_nf5);;

(* Lean: f4_northeast_g7 *)
let C983F4CE_F4_NORTHEAST_G7 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 4 7] (c983f4f_mem 17 6)) (c983f4ce_g7 ());;

let c983f4ce_g7th () = c983f5_use C983F4CE_F4_NORTHEAST_G7 [c983f4ce_f4 ()];;

(* Lean: f4_top_avoids_g7 *)
let C983F4CE_F4_TOP_AVOIDS_G7 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 4 7] (mk_neg (c983f4f_mem 17 11)))
  (c983f4f_absent 6 11 (c983f4ce_g7th ()));;

(* Lean: f4_top_avoids_f5 *)
let c983f4ce_avoids_f5 () =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f4 = c983f4ce_f4 () in
  let marker = seed 11 `&2` `&1543 / &500` in
  let inward = c983sa_aux 5 11 in
  let rat t = EQT_ELIM (REAL_RAT_REDUCE_CONV t) in
  let tb yv =
    MP (SPECL (c983ab_own 32768 @ [`&2`; `&113 / &50`; `&1543 / &500`; yv]) OO_VERTICAL_SEGMENT)
       (end_itlist CONJ [inward; marker; rat `&113 / &50 < &1543 / &500`;
                         rat (mk_binop `(<=):real->real->bool` `&113 / &50` yv);
                         rat (mk_binop `(<=):real->real->bool` yv `&1543 / &500`)]) in
  let rbar = c983f5_use C983FO_F4_RIGHT_BAR [f4] in
  let rb yv = MP (MP (SPEC yv rbar) (rat (mk_binop `(<=):real->real->bool` `&113 / &50` yv)))
                 (rat (mk_binop `(<=):real->real->bool` yv `&64 / &25`)) in
  let nTop = c983f4f_point (c983f4ce_g7th ()) in
  let facts = [unit 1024; pos; side; seed 6 `&47 / &20` `&47 / &20`; nTop;
               excl 1024 32768 (tb `&12 / &5`); excl 1024 32768 (tb `&3`);
               excl 1024 16384 (rb `&12 / &5`); excl 1024 48 (seed 3 `&3` `&3`);
               excl 1024 16384 (rb `&64 / &25`)] in
  let point = c983sa_apply C983FO_CONV (SPECL (c983ab_own 1024) C981UP_POINT) facts in
  let f = c983f4ce_apart_at 1024 32768 (`&2`, `&131 / &50`) point (tb `&131 / &50`) in
  NOT_INTRO (DISCH (c983f4f_mem 5 11) f);;

let C983F4CE_F4_TOP_AVOIDS_F5 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 4 7] (mk_neg (c983f4f_mem 5 11))) (c983f4ce_avoids_f5 ());;

(* Lean: top_exact_check (private) *)
let C983F4CE_TOP_EXACT_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(7 IN s) ==> ~(17 IN s) ==> ~(5 IN s) ==>
       s = {3, 14}`, c983f5_check []);;

(* Lean: f4_top_exact *)
let C983F4CE_F4_TOP_EXACT =
  let f4 = c983f4ce_f4 () in
  c983f4f_close (c983sa_stmt [c983f4f_mem 4 7] (mk_eq(c983f4f_act 11, `{3, 14}`)))
    (c983f5_mps (MATCH_MP C983F4CE_TOP_EXACT_CHECK (c983f4f_orig 11))
       [c983f5_use C983F4F_F4_TOP_AVOIDS_F7 [f4]; c983f5_use C983F4CE_F4_TOP_AVOIDS_G7 [f4];
        c983f5_use C983F4CE_F4_TOP_AVOIDS_F5 [f4]]);;

(* Lean: southeast_outward_g8_check (private) *)
let C983F4CE_SOUTHEAST_OUTWARD_G8_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(16 IN s) ==> 18 IN s`, c983f5_check []);;

(* Lean: f4_outward_northeast_f5 *)
let C983F4CE_F4_OUTWARD_NORTHEAST_F5 =
  let f4 = c983f4ce_f4 () in
  let noG6 = ASSUME (mk_neg (c983f4f_mem 16 5)) and noF5 = ASSUME (mk_neg (c983f4f_mem 5 6)) in
  let nF7 = c983f5_res_left (CONJUNCT1 (c983f5_use C983F4F_F4_NORTHEAST [f4])) noF5 in
  let g8 = MP (MATCH_MP C983F4CE_SOUTHEAST_OUTWARD_G8_CHECK (c983f4f_orig 5)) noG6 in
  let lower = c983f5_use C983SA_SOUTHEAST_OUTWARD_POINT [c983f5_use C983F4F_F4_SOUTHEAST [f4]; g8; noG6] in
  let upper = c983f5_use C983SA_NORTHEAST_UPPER_POINT
    [nF7; noF5; c983f5_use C983FO_F4_TOP_ORIGIN [f4]; c983f5_use C983FO_F4_RIGHT_BAR [f4]] in
  let f = c983f4ce_apart_at 512 1024 (`&101 / &40`, `&17 / &8`) lower upper in
  c983f4f_close (c983sa_stmt [c983f4f_mem 4 7; mk_neg (c983f4f_mem 16 5)] (c983f4f_mem 5 6))
    (CCONTR (c983f4f_mem 5 6) f);;

(* Lean: two_inward_southeast_check (private) *)
let C983F4CE_TWO_INWARD_SOUTHEAST_CHECK = prove
 (`forall s. MEM s c983f5_southeast_components ==> ~(4 IN s) ==> 8 IN s ==> s = {8, 16} \/ s = {8, 16, 18}`,
  c983f5_check [c983f5_southeast_components]);;

(* Lean: two_inward_central *)
let C983F4CE_TWO_INWARD_CENTRAL =
  let f4 = c983f4ce_f4 () and f5 = ASSUME (c983f4f_mem 5 7) in
  let upper = c983f5_use C983F5_F5_UPPER_OF_RIGHT_G9 [f5; CONJUNCT2 (c983f5_use C983F4F_F4_RIGHT [f4])] in
  let se = c983f5_mps (MATCH_MP C983F4CE_TWO_INWARD_SOUTHEAST_CHECK
                         (c983f5_use C983F5_F5_SOUTHEAST_COMPONENTS [f5]))
             [c983f4f_absent 7 5 f4; c983f5_use C983F4F_F4_SOUTHEAST [f4]] in
  c983f4f_close
    (c983sa_stmt [c983f4f_mem 4 7; c983f4f_mem 5 7]
       (mk_conj(mk_disj(mk_eq(c983f4f_act 5, `{8, 16}`), mk_eq(c983f4f_act 5, `{8, 16, 18}`)),
                mk_conj(mk_eq(c983f4f_act 6, `{7, 17}`), mk_eq(c983f4f_act 11, `{3, 14}`)))))
    (CONJ se upper);;
