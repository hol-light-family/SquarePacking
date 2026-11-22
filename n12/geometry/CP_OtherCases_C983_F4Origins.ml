(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4Origins.lean.               *)
(* Actual C983 wall origins and bars.  owners p 4 / 5 / 6 / 8 / 10 / 11 =    *)
(* owner 192 / 512 / 1024 / 4096 / 16384 / 32768; actual p i =              *)
(* c983e_actual c1 c2 a b l i.  pullX / pullY are the tuples of             *)
(* LINSIDE_PULLX / LINSIDE_PULLY (container_pullX = LCONT_PULLX; the needed  *)
(* coordinate bounds of container_pullY are C983FO_PY_BOX_B / _K).          *)
(* WallProfile.boundary_origin = OCWPBO_BOUNDARY_ORIGIN,                     *)
(* WallUpperMissingReach.point = WUMR_POINT, vertical_segment =              *)
(* OO_VERTICAL_SEGMENT.  Tag C983FO_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4Filters.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

let C983FO_PY_BOX_B = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c (--s) (u - &4 * s) (&4 * c - v - a) a x y ==> &0 <= y`,
  REWRITE_TAC[lcont; LINSIDE_PULLY] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN REAL_ARITH_TAC);;

let C983FO_PY_BOX_K = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c (--s) (u - &4 * s) (&4 * c - v - a) a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont; LINSIDE_PULLY] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN REAL_ARITH_TAC);;

(* the pulled tuple of an owner (the arguments of the LHS of LINSIDE_PULLX / LINSIDE_PULLY) *)
let c983fo_pull pth m =
  let t = SPECL (c983ab_own m @ [`x:real`; `y:real`]) pth in
  let args = snd (strip_comb (lhs (concl t))) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;

let C983FO_CONV = REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; REAL_NEG_MUL2] THENC
                  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* discharge the antecedents of a specialised lemma from facts (up to the pull conversions) *)
let c983fo_apply spec facts =
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = C983FO_CONV tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) facts)
    with Failure _ -> failwith ("c983fo_apply: " ^ string_of_term tm) in
  let th = MP spec (end_itlist CONJ (map pa ants)) in
  EQ_MP (C983FO_CONV (concl th)) th;;

let c983fo_facts () =
  let np = ASSUME C983F4F_NP and hh = c983f4f_hh () in
  let side = MP (SPECL C983E_VARS OO_SIDE) np in
  let pos = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  let unit m = MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let box m = MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_BOX) np in
  let seed i x y = MP (SPECL C983E_VARS (c983e_seed_inside i (x, y))) hh in
  let apart m n = REWRITE_RULE[ldisj] (MP (SPECL C983E_VARS (oo_apart C983E_F m n)) hh) in
  let excl m n pt =
    let args = snd (strip_comb (concl pt)) in
    let d2 = SPECL [el 5 args; el 6 args] (apart m n) in
    let a = lhand (rand (concl d2)) in
    NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt))) in
  (side, pos, unit, box, seed, apart, excl);;

(* Lean: top_origin_of_f3 *)
let c983fo_top_origin f3 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hh = c983f4f_hh () in
  let inner = c983f4f_point f3 in
  let foreign = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (MP (MP (SPEC `&5 / &2` (MP (SPECL C983E_VARS C983AB_LEFT_BAR) hh))
            (EQT_ELIM (REAL_RAT_REDUCE_CONV `&113 / &50 <= &5 / &2`)))
        (EQT_ELIM (REAL_RAT_REDUCE_CONV `&5 / &2 <= &14 / &5`))) in
  let missing = excl 192 4096 foreign in
  let pB = c983fo_pull LINSIDE_PULLY 32768 and pK = c983fo_pull LINSIDE_PULLY 192 in
  let disj =
    let tm = list_mk_comb(`ldisj`, pK @ pB) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; LINSIDE_PULLY] tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`x:real`; `&4 - y`] (apart 192 32768)))) in
  let facts = [unit 32768; unit 192; pos; side; REFL `l:real`;
               MATCH_MP C983FO_PY_BOX_B (box 32768); MATCH_MP C983FO_PY_BOX_K (box 192);
               seed 11 `&2` `&1543 / &500`; inner; seed 4 `&1` `&1543 / &500`; seed 4 `&1` `&3`;
               missing; disj] in
  c983fo_apply (SPECL (pB @ pK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN) facts;;

let C983FO_TOP_ORIGIN_OF_F3 = c983f4f_close
  (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj [C983F4F_NP; C983F4F_IMG; c983f4f_mem 3 11], c983ab_in 32768 `&2` `&3`))))
  (c983fo_top_origin (ASSUME (c983f4f_mem 3 11)));;

(* Lean: f4_top_origin *)
let C983FO_F4_TOP_ORIGIN = c983f4f_close
  (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj [C983F4F_NP; C983F4F_IMG; c983f4f_mem 4 7], c983ab_in 32768 `&2` `&3`))))
  (c983fo_top_origin (CONJUNCT1 (MP (SPECL C983E_VARS C983F4F_F4_TOP)
     (CONJ (ASSUME C983F4F_NP) (CONJ (ASSUME C983F4F_IMG) (ASSUME (c983f4f_mem 4 7)))))));;

(* Lean: right_advance_of_f8 *)
let c983fo_right_advance f8 g9 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let upper = c983f4f_point g9 in
  let southeast = c983f4f_point f8 in
  let missingF = excl 16384 512 southeast in
  let missingM = excl 16384 1024 (seed 6 `&47 / &20` `&47 / &20`) in
  let pR = c983fo_pull LINSIDE_PULLX 16384 in
  let facts = [unit 16384; pos; side; MATCH_MP LCONT_PULLX (box 16384);
               seed 10 `&1543 / &500` `&2`; upper; missingF; missingM] in
  c983fo_apply (SPECL pR WUMR_POINT) facts;;

let C983FO_RIGHT_ADVANCE_OF_F8 = c983f4f_close
  (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj [C983F4F_NP; C983F4F_IMG; c983f4f_mem 8 5; c983f4f_mem 19 10],
           c983ab_in 16384 `&3` `&64 / &25`))))
  (c983fo_right_advance (ASSUME (c983f4f_mem 8 5)) (ASSUME (c983f4f_mem 19 10)));;

(* Lean: right_bar_of_f8 *)
let c983fo_right_bar f8 f9 g9 =
  let low = c983f4f_point f9 in
  let adv = c983fo_right_advance f8 g9 in
  let lower = `&113 / &50 <= y` and upper = `y <= &64 / &25` in
  let th = MP (SPECL (c983ab_own 16384 @ [`&3`; `&113 / &50`; `&64 / &25`; `y:real`]) OO_VERTICAL_SEGMENT)
              (end_itlist CONJ [low; adv; EQT_ELIM (REAL_RAT_REDUCE_CONV `&113 / &50 < &64 / &25`);
                                ASSUME lower; ASSUME upper]) in
  GEN `y:real` (DISCH lower (DISCH upper th));;

let c983fo_bar_stmt hyps = mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj ([C983F4F_NP; C983F4F_IMG] @ hyps),
      mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &64 / &25`, c983ab_in 16384 `&3` `y:real`))))));;

let C983FO_RIGHT_BAR_OF_F8 = c983f4f_close
  (c983fo_bar_stmt [c983f4f_mem 8 5; c983f4f_mem 9 10; c983f4f_mem 19 10])
  (c983fo_right_bar (ASSUME (c983f4f_mem 8 5)) (ASSUME (c983f4f_mem 9 10)) (ASSUME (c983f4f_mem 19 10)));;

(* Lean: f4_right_bar *)
let C983FO_F4_RIGHT_BAR =
  let h3 = CONJ (ASSUME C983F4F_NP) (CONJ (ASSUME C983F4F_IMG) (ASSUME (c983f4f_mem 4 7))) in
  let r = MP (SPECL C983E_VARS C983F4F_F4_RIGHT) h3 in
  let s = MP (SPECL C983E_VARS C983F4F_F4_SOUTHEAST) h3 in
  c983f4f_close (c983fo_bar_stmt [c983f4f_mem 4 7])
    (c983fo_right_bar s (CONJUNCT1 r) (CONJUNCT2 r));;
