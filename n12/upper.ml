(* ========================================================================= *)
(* Twelve unit squares fit in a square of side 4 (the 4 x 3 grid).           *)
(* ========================================================================= *)

needs "shared/squares_lib.ml";;

let grid_sq = new_definition
 `grid_sq k = sqbox (vector[&(k DIV 3); &(k MOD 3)]) (vector[&1; &0]) (vector[&0; &1])`;;

let IN_AXIS_SQBOX = prove
 (`forall a b x:real^2. x IN sqbox (vector[a; b]) (vector[&1; &0]) (vector[&0; &1]) <=>
                  a <= x$1 /\ x$1 <= a + &1 /\ b <= x$2 /\ x$2 <= b + &1`,
  REWRITE_TAC[sqbox; IN_ELIM_THM; DOT_2; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let AXIS_SQBOX_DISJOINT = prove
 (`forall a b c d. a + &1 <= c \/ c + &1 <= a \/ b + &1 <= d \/ d + &1 <= b
             ==> DISJOINT
                  (interior(sqbox (vector[a; b]) (vector[&1; &0]) (vector[&0; &1])))
                  (interior(sqbox (vector[c; d]) (vector[&1; &0]) (vector[&0; &1])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC DISJOINT_INTERIORS_SEPARATED THEN
    MAP_EVERY EXISTS_TAC [`vector[&1; &0]:real^2`; `c:real`];
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    MATCH_MP_TAC DISJOINT_INTERIORS_SEPARATED THEN
    MAP_EVERY EXISTS_TAC [`vector[&1; &0]:real^2`; `a:real`];
    MATCH_MP_TAC DISJOINT_INTERIORS_SEPARATED THEN
    MAP_EVERY EXISTS_TAC [`vector[&0; &1]:real^2`; `d:real`];
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    MATCH_MP_TAC DISJOINT_INTERIORS_SEPARATED THEN
    MAP_EVERY EXISTS_TAC [`vector[&0; &1]:real^2`; `b:real`]] THEN
  REWRITE_TAC[IN_AXIS_SQBOX; DOT_2; VECTOR_2; CART_EQ; DIMINDEX_2; FORALL_2;
              VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let PACKS_12_4 = prove
 (`packs 12 (&4)`,
  REWRITE_TAC[packs] THEN EXISTS_TAC `grid_sq` THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[grid_sq] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOX_IMP_UNIT_SQUARE THEN REWRITE_TAC[DOT_2; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_AXIS_SQBOX; IN_CONTAINER] THEN
    SUBGOAL_THEN `&(k DIV 3) <= &3 /\ &(k MOD 3) <= &2` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[ARITH_RULE `k < 12 ==> k DIV 3 <= 3`];
                      MP_TAC(SPECL [`k:num`; `3`] DIVISION) THEN ARITH_TAC];
      MP_TAC(SPEC `k DIV 3` REAL_POS) THEN MP_TAC(SPEC `k MOD 3` REAL_POS) THEN
      REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`k:num`; `l:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[grid_sq] THEN MATCH_MP_TAC AXIS_SQBOX_DISJOINT THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `~(k DIV 3 = l DIV 3) \/ ~(k MOD 3 = l MOD 3)` MP_TAC THENL
     [MP_TAC(SPECL [`k:num`; `3`] DIVISION) THEN
      MP_TAC(SPECL [`l:num`; `3`] DIVISION) THEN
      REWRITE_TAC[ARITH_EQ] THEN
      UNDISCH_TAC `~(k:num = l)` THEN MESON_TAC[];
      ARITH_TAC]]);;
