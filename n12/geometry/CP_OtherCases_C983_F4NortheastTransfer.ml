(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4NortheastTransfer.lean       *)
(* (N12Compact.Completion.OtherCases.C983).  The two genuine northeast       *)
(* alternatives supply an actual sharp point and the right-wall origin.      *)
(* Conventions of CP_OtherCases_C983_F4Origins.ml / F4Filters.ml (statements *)
(* c983sa_stmt; owners p 2 / 3 / 5 / 6 / 7 / 10 / 11 = owner 12 / 48 / 512 /  *)
(* 1024 / 2304 / 16384 / 32768; j IN actual p i is c983f4f_mem j i, its      *)
(* point via c983f4f_point).  (owners p 6).translated 2 2 is the tuple       *)
(* C983FNT_T6 (equivalence C983FNT_EQ6).  positive_mixed_transfer            *)
(* C983PMT_POSITIVE_MIXED_TRANSFER; C1090 ResidualCentralPoints.mixed_point  *)
(* C1090RCP_MIXED_POINT; f4_northeast_g7 C983F4CE_F4_NORTHEAST_G7;           *)
(* f4_southeast_g6 C983F4OJ_F4_SOUTHEAST_G6; f4_merged_center                *)
(* C983FCE_F4_MERGED_CENTER; f4_top_origin C983FO_F4_TOP_ORIGIN;             *)
(* f4_southeast_crosspoint C983F4CF_F4_SOUTHEAST_CROSSPOINT;                 *)
(* f4_top_only_points C983TOP_F4_TOP_ONLY_POINTS; f4_right C983F4F_F4_RIGHT; *)
(* f4_right_bar C983FO_F4_RIGHT_BAR; right_origin_of_upper_extension         *)
(* C983WO_RIGHT_ORIGIN_OF_UPPER_EXTENSION.  Tag C983FNT_.                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4CornerEntrance.ml";;
needs "n12/geometry/CP_OtherCases_C983_PositiveMixedTransfer.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualCentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4CentralEntrance.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4CentralFinal.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4OutwardJoin.ml";;
needs "n12/geometry/CP_OtherCases_C983_WallOrigins.ml";;
needs "n12/geometry/CP_OtherCases_C983_TopOnlyPoints.ml";;

let C983FNT_LIN = NLIN_TAC ~deg2:false [];;
let C983FNT_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;
let C983FNT_MUL_TAC =
  (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN RASM_ARITH_TAC;;
let C983FNT_OPEN_TAC tm =
  STRIP_ASSUME_TAC (REWRITE_RULE[linside] (ASSUME tm));;
(* a missing point from a strict linear violation of its face *)
let C983FNT_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C983FNT_LIN;;

(* Lean: negative_mixed_transfer *)
let C983FNT_NEGATIVE_MIXED_TRANSFER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\ linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1 / &2) (&0)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983FNT_FACT `c <= &1` (NLIN_TAC [SQ_NONNEG `s:real`]) THEN
  C983FNT_FACT `c + --s <= &3 / &2` (NLIN_TAC [SQ_NONNEG `c + s:real`]) THEN
  C983FNT_OPEN_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
  C983FNT_OPEN_TAC `linside c s u v a (&0) (&13 / &50)` THEN
  C983FNT_OPEN_TAC `linside c s u v a (&13 / &50) (&1)` THEN
  C983FNT_FACT `s <= u`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FNT_MISS_TAC `~linside c s u v a (&0) (&1)`) THEN
  C983FNT_FACT `&13 / &50 * --s <= v`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FNT_MISS_TAC `~linside c s u v a (&13 / &50) (&0)`) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C983FNT_FACT `v + a <= --s / &2 + c`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FNT_MISS_TAC `~linside c s u v a (&1 / &2) (&1)`) THEN
  C983FNT_FACT `u + a <= c / &2`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FNT_MISS_TAC `~linside c s u v a (&1 / &2) (&0)`) THEN
  C983FNT_FACT `&3 / &4 * c < --s`
   (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983FNT_FACT `&0 <= c * (&3 / &4 * c - --s)` C983FNT_MUL_TAC THEN
    C983FNT_FACT `&1 < c / &2 + --s` C983FNT_LIN THEN
    C983FNT_FACT `&0 < (c / &2 + --s - &1) * (c / &2 + --s + &1)` C983FNT_MUL_TAC THEN
    C983FNT_LIN) THEN
  C983FNT_FACT `&1 < c + &6 / &25 * --s` C983FNT_LIN THEN
  C983FNT_FACT `&0 < (c + &6 / &25 * --s - &1) * (c + &6 / &25 * --s + &1)` C983FNT_MUL_TAC THEN
  C983FNT_FACT `&0 <= --s * (&589 / &625 * --s - &12 / &25 * c)` C983FNT_MUL_TAC THEN
  C983FNT_LIN);;

(* (owners p 6).translated 2 2 and its plain equivalence *)
let C983FNT_T6 =
  match c983ab_own 1024 with
    [c; s; u; v; a] ->
      [c; s; mk_binop `(-):real->real->real` u
               (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c `&2`)
                                                (mk_binop `( * ):real->real->real` s `&2`));
       mk_binop `(-):real->real->real` v
               (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, s)) `&2`)
                                                (mk_binop `( * ):real->real->real` c `&2`)); a]
  | _ -> failwith "C983FNT_T6";;
let C983FNT_EQ6 =
  let x = `x:real` and y = `y:real` in
  prove(list_mk_forall([x; y], mk_eq(list_mk_comb(`linside`, C983FNT_T6 @ [x; y]),
          list_mk_comb(`linside`, c983ab_own 1024 @ [`&2 + x`; `&2 + y`]))),
        REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C983FNT_NV = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `l:real`];;
let c983fnt_nin x y = list_mk_comb(`linside`, C983FNT_NV @ [x; y]);;
let C983FNT_ACT =
  let x = `x:real` and y = `y:real` in
  list_mk_forall([x; y], mk_eq(c983fnt_nin x y,
    list_mk_comb(`linside`, c983ab_own 1024 @ [`&2 + x`; `&2 + y`])));;
let c983fnt_cf eq tm th =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[eq] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    (fun g -> try ACCEPT_TAC th g with Failure _ ->
       failwith ("c983fnt_cf: " ^ string_of_term (snd g) ^ " FROM " ^ string_of_term (concl th)));
    ALL_TAC];;
let C983FNT_CLOSE_TAC =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; RASM_ARITH_TAC];;

let c983fnt_unit_of uth t =
  let c = el 0 t and s = el 1 t in
  let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                   (mk_binop `( * ):real->real->real` s s), `&1`) in
  MP (prove(mk_imp(concl uth, tm), CONV_TAC REAL_RING)) uth;;

let C983FNT_F4 = c983f4f_mem 4 7 and C983FNT_MIXED = c983f4f_mem 5 6;;

(* Lean: f4_northeast_extension *)
let C983FNT_F4_NORTHEAST_EXTENSION = prove
 (c983sa_stmt [C983FNT_F4] (c983ab_in 1024 `&5 / &2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC C983FNT_MIXED THENL
   [ALL_TAC;
    MP_TAC(SPECL C983E_VARS C983TOP_F4_TOP_ONLY_POINTS) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]] THEN
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f4 = ASSUME C983FNT_F4 in
  let use th = c983f5_use th [f4] in
  let marker = seed 6 `&47 / &20` `&47 / &20` in
  let near = c983f4f_point (ASSUME C983FNT_MIXED) in
  let far = c983f4f_point (use C983F4CE_F4_NORTHEAST_G7) in
  let elbow = c983f4f_point (use C983F4OJ_F4_SOUTHEAST_G6) in
  let center = use C983FCE_F4_MERGED_CENTER and top = use C983FO_F4_TOP_ORIGIN in
  let cross = use C983F4CF_F4_SOUTHEAST_CROSSPOINT in
  let act = ASSUME C983FNT_ACT in
  MP_TAC(MP (SPECL C983FNT_T6 CLF_CANONICAL_FRAME)
            (CONJ (c983fnt_unit_of (unit 1024) C983FNT_T6) pos)) THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  SUBGOAL_THEN C983FNT_ACT ASSUME_TAC THENL
   [REWRITE_TAC[GSYM C983FNT_EQ6] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (fun th -> is_forall (concl th)));
    ALL_TAC] THEN
  ASSUME_TAC side THEN ASSUME_TAC pos THEN
  c983fnt_cf act (c983fnt_nin `&7 / &20` `&7 / &20`) marker THEN
  c983fnt_cf act (c983fnt_nin `&0` `&13 / &50`) near THEN
  c983fnt_cf act (c983fnt_nin `&13 / &50` `&1`) far THEN
  c983fnt_cf act (mk_neg (c983fnt_nin `&0` `&0`)) (excl 1024 2304 center) THEN
  c983fnt_cf act (mk_neg (c983fnt_nin `&0` `&1`)) (excl 1024 32768 top) THEN
  c983fnt_cf act (mk_neg (c983fnt_nin `&13 / &50` `&0`)) (excl 1024 512 elbow) THEN
  c983fnt_cf act (mk_neg (c983fnt_nin `&1 / &2` `&0`)) (excl 1024 512 cross) THEN
  SUBGOAL_THEN (c983fnt_nin `&1 / &2` `&1`) MP_TAC THENL
   [ASM_CASES_TAC `&0 <= sN` THENL
     [MP_TAC(SPECL C983FNT_NV C983PMT_POSITIVE_MIXED_TRANSFER) THEN
      ANTS_TAC THENL [C983FNT_CLOSE_TAC; SIMP_TAC[]];
      MP_TAC(SPECL C983FNT_NV C983FNT_NEGATIVE_MIXED_TRANSFER) THEN
      ANTS_TAC THENL [C983FNT_CLOSE_TAC; SIMP_TAC[]]];
    REWRITE_TAC[act] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[]]);;

(* Lean: f4_right_origin *)
let C983FNT_F4_RIGHT_ORIGIN = prove
 (c983sa_stmt [C983FNT_F4] (c983ab_in 16384 `&3` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C983E_VARS C983WO_RIGHT_ORIGIN_OF_UPPER_EXTENSION) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL C983E_VARS C983F4F_F4_RIGHT) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(SPECL C983E_VARS C983FNT_F4_NORTHEAST_EXTENSION) THEN ASM_REWRITE_TAC[]]);;

(* Lean: f4_northeast_sharp *)
let C983FNT_F4_NORTHEAST_SHARP = prove
 (c983sa_stmt [C983FNT_F4]
    (mk_disj(c983ab_in 1024 `&101 / &40` `&17 / &8`, c983ab_in 1024 `&121 / &50` `&54 / &25`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC C983FNT_MIXED THENL
   [ALL_TAC;
    DISJ1_TAC THEN MP_TAC(SPECL C983E_VARS C983TOP_F4_TOP_ONLY_POINTS) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]] THEN
  DISJ2_TAC THEN
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f4 = ASSUME C983FNT_F4 in
  let use th = c983f5_use th [f4] in
  let near = c983f4f_point (ASSUME C983FNT_MIXED) in
  let far = c983f4f_point (use C983F4CE_F4_NORTHEAST_G7) in
  let top = use C983FO_F4_TOP_ORIGIN in
  let right = MP (MP (SPEC `&113 / &50` (use C983FO_F4_RIGHT_BAR))
                     (REAL_ARITH `&113 / &50 <= &113 / &50`))
                 (REAL_ARITH `&113 / &50 <= &64 / &25`) in
  let eq = C983FNT_EQ6 in
  let t6 = C983FNT_T6 in
  let tin x y = list_mk_comb(`linside`, t6 @ [x; y]) in
  ASSUME_TAC side THEN ASSUME_TAC pos THEN ASSUME_TAC (c983fnt_unit_of (unit 1024) t6) THEN
  c983fnt_cf eq (tin `&7 / &20` `&7 / &20`) (seed 6 `&47 / &20` `&47 / &20`) THEN
  c983fnt_cf eq (tin `&0` `&13 / &50`) near THEN
  c983fnt_cf eq (tin `&13 / &50` `&1`) far THEN
  c983fnt_cf eq (mk_neg (tin `--(&7 / &20)` `&7 / &20`)) (excl 1024 2304 (seed 7 `&33 / &20` `&47 / &20`)) THEN
  c983fnt_cf eq (mk_neg (tin `&0` `&1`)) (excl 1024 32768 top) THEN
  c983fnt_cf eq (mk_neg (tin `&1` `&1`)) (excl 1024 48 (seed 3 `&3` `&3`)) THEN
  c983fnt_cf eq (mk_neg (tin `&1` `&13 / &50`)) (excl 1024 16384 right) THEN
  MP_TAC(SPECL t6 C1090RCP_MIXED_POINT) THEN
  ANTS_TAC THENL [C983FNT_CLOSE_TAC; ALL_TAC] THEN
  REWRITE_TAC[eq] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[]);;
