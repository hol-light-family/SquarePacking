(* ========================================================================= *)
(* Port, layer 5: from a normalized packing to a VALIDF family (Jatloe:      *)
(* PackingBridge, PackingBudget, Budget).  The hull-conflict condition is    *)
(* kept as a hypothesis here; it is discharged in hull.ml.                   *)
(* ========================================================================= *)

needs "n12/phase1/normalize.ml";;
needs "n12/phase1/groups.ml";;
needs "n12/phase1/families.ml";;
needs "n12/phase1/auxcover.ml";;

let FFP = new_definition
 `FFP (c1:num->real) c2 a b l =
    IMAGE (\i. owned (c1 i) (c2 i) (a i) (b i) l) {i | i < 12}`;;

let NPACK_SQ = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12
     ==> &1 < l /\ l <= &1001 / &1000 /\ a i * a i + b i * b i = &1 /\
         owalls (c1 i) (c2 i) (a i) (b i) l`,
  SIMP_TAC[NPACK]);;

let NPACK_DISJ = prove
 (`forall c1 c2 a b l i j z. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\
       z IN osq (c1 i) (c2 i) (a i) (b i) l /\ z IN osq (c1 j) (c2 j) (a j) (b j) l
       ==> i = j`,
  REWRITE_TAC[NPACK; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let OWNED_NONEMPTY = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12
     ==> exists k. k IN owned (c1 i) (c2 i) (a i) (b i) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[owned; IN_ELIM_THM] THEN
  MATCH_MP_TAC MARKER_NONAVOID THEN ASM_MESON_TAC[NPACK_SQ]);;

let OWNED_INJ = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\
       owned (c1 i) (c2 i) (a i) (b i) l = owned (c1 j) (c2 j) (a j) (b j) l
       ==> i = j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                `l:real`; `i:num`] OWNED_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `k IN owned (c1 (i:num)) (c2 i) (a i) (b i) l` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `k IN owned (c1 (j:num)) (c2 j) (a j) (b j) l` THEN
  REWRITE_TAC[owned; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NPACK_DISJ THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                        `l:real`; `marker k`] THEN
  ASM_REWRITE_TAC[]);;

let FINITE_LT12 = prove(`FINITE {i:num | i < 12}`, REWRITE_TAC[FINITE_NUMSEG_LT]);;

let FFP_CARD = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> FINITE (FFP c1 c2 a b l) /\ CARD (FFP c1 c2 a b l) = 12`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FFP] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_LT12] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `CARD {i:num | i < 12}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_LT12; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OWNED_INJ];
    REWRITE_TAC[CARD_NUMSEG_LT]]);;

let FFP_DISJ = prove
 (`forall c1 c2 a b l G H. NPACK c1 c2 a b l /\ G IN FFP c1 c2 a b l /\ H IN FFP c1 c2 a b l /\
       ~(G = H) ==> DISJOINT G H`,
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th))))) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[owned; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x:num = x'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC NPACK_DISJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                          `l:real`; `marker k`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* The 103 masks are the bit codes of the 103 cliques, in order. *)

let CANDMASKS_CLQ = prove
 (`MAP (\c. ITLIST (\k a. 2 EXP k + a) c 0) CLQ = CANDMASKS`,
  REWRITE_TAC[CLQ; CANDMASKS; MAP; ITLIST] THEN CONV_TAC NUM_REDUCE_CONV);;

let BINARYSUM_INJ = prove
 (`forall s t. FINITE s /\ FINITE t /\ binarysum s = binarysum t ==> s = t`,
  MESON_TAC[BITSET_BINARYSUM]);;

let FINITE_OWNED = prove
 (`forall c1 c2 a b l. FINITE (owned c1 c2 a b l)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{k:num | k < 16}` THEN REWRITE_TAC[FINITE_NUMSEG_LT; owned] THEN SET_TAC[]);;

let FFP_CLQ = prove
 (`forall c1 c2 a b l G. NPACK c1 c2 a b l /\ G IN FFP c1 c2 a b l
     ==> exists c. MEM c CLQ /\ G = set_of_list c`,
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(SPECL [`(c1:num->real) x`; `(c2:num->real) x`; `(a:num->real) x`;
                `(b:num->real) x`; `l:real`] OWNMASK_IN_TABLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[NPACK_SQ]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CANDMASKS_CLQ; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:num list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BINARYSUM_INJ THEN REWRITE_TAC[FINITE_OWNED; FINITE_SET_OF_LIST] THEN
  ASM_REWRITE_TAC[GSYM ownmask] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC BINARYSUM_LIST THEN ASM_MESON_TAC[CLQ_PROP]);;

(* ------------------------------------------------------------------------- *)
(* Pair budgets.                                                             *)
(* ------------------------------------------------------------------------- *)

let BUDGET_LEMMA = prove
 (`forall (E:num->bool) (own:num->num->bool).
      (forall i. i < 12 /\ ~(i IN E) ==> exists j. j < 10 /\ own i j) /\
      (forall i i' j. i < 12 /\ i' < 12 /\ own i j /\ own i' j ==> i = i')
      ==> 2 <= CARD {i | i < 12 /\ i IN E}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `f:num->num`) THEN
  SUBGOAL_THEN `CARD {i | i < 12 /\ ~(i IN E)} <= CARD {j:num | j < 10}` MP_TAC THENL
   [MATCH_MP_TAC CARD_INJ_LE THEN EXISTS_TAC `f:num->num` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < 12}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG_LT] THEN
  SUBGOAL_THEN `CARD {i | i < 12 /\ i IN E} + CARD {i | i < 12 /\ ~(i IN E)} =
                CARD {i:num | i < 12}` MP_TAC THENL
   [MATCH_MP_TAC CARD_UNION_EQ THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    REWRITE_TAC[CARD_NUMSEG_LT] THEN ARITH_TAC]);;

let FPT_LIST = `[vector[&1; &87 / &50]; vector[&1; &113 / &50]; vector[&8 / &5; &1];
                 vector[&8 / &5; &3]; vector[&2; &87 / &50]; vector[&2; &113 / &50];
                 vector[&12 / &5; &1]; vector[&12 / &5; &3]; vector[&3; &87 / &50];
                 vector[&3; &113 / &50]]:(real^2)list`;;
let fpt = new_definition (mk_eq(`fpt (j:num):real^2`, mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, `j:num`), FPT_LIST)));;
let gpt = new_definition `gpt (j:num) = vector[fpt j$2; fpt j$1]:real^2`;;

let LT10_CASES = prove
 (`forall j. j < 10 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/
                  j = 7 \/ j = 8 \/ j = 9`, ARITH_TAC);;

let FPT_EXPLICIT = prove
 (`forall c. (forall j. j < 10 ==> ~(fpt j IN c)) <=>
         ~(vector[&1; &87 / &50] IN c) /\ ~(vector[&1; &113 / &50] IN c) /\
         ~(vector[&8 / &5; &1] IN c) /\ ~(vector[&8 / &5; &3] IN c) /\
         ~(vector[&2; &87 / &50] IN c) /\ ~(vector[&2; &113 / &50] IN c) /\
         ~(vector[&12 / &5; &1] IN c) /\ ~(vector[&12 / &5; &3] IN c) /\
         ~(vector[&3; &87 / &50] IN c) /\ ~(vector[&3; &113 / &50] IN c)`,
  REWRITE_TAC[LT10_CASES; fpt] THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let GPT_EXPLICIT = prove
 (`forall c. (forall j. j < 10 ==> ~(gpt j IN c)) <=>
         ~(vector[&87 / &50; &1] IN c) /\ ~(vector[&113 / &50; &1] IN c) /\
         ~(vector[&1; &8 / &5] IN c) /\ ~(vector[&3; &8 / &5] IN c) /\
         ~(vector[&87 / &50; &2] IN c) /\ ~(vector[&113 / &50; &2] IN c) /\
         ~(vector[&1; &12 / &5] IN c) /\ ~(vector[&3; &12 / &5] IN c) /\
         ~(vector[&87 / &50; &3] IN c) /\ ~(vector[&113 / &50; &3] IN c)`,
  REWRITE_TAC[LT10_CASES; gpt; fpt] THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[VECTOR_2]);;

let PAIRIN_F_EXPLICIT = prove
 (`forall c1 c2 a b l. pairin FPAIRS (owned c1 c2 a b l) <=>
     (vector[&1; &457 / &500] IN osq c1 c2 a b l /\ vector[&457 / &500; &1] IN osq c1 c2 a b l) \/
     (vector[&3; &457 / &500] IN osq c1 c2 a b l /\ vector[&1543 / &500; &1] IN osq c1 c2 a b l) \/
     (vector[&3; &1543 / &500] IN osq c1 c2 a b l /\ vector[&1543 / &500; &3] IN osq c1 c2 a b l) \/
     (vector[&1; &1543 / &500] IN osq c1 c2 a b l /\ vector[&457 / &500; &3] IN osq c1 c2 a b l) \/
     (vector[&33 / &20; &33 / &20] IN osq c1 c2 a b l /\ vector[&33 / &20; &47 / &20] IN osq c1 c2 a b l) \/
     (vector[&47 / &20; &33 / &20] IN osq c1 c2 a b l /\ vector[&47 / &20; &47 / &20] IN osq c1 c2 a b l)`,
  REWRITE_TAC[pairin; FPAIRS; EX; owned; IN_ELIM_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MARKER_EXPLICIT; OR_CLAUSES]);;

let PAIRIN_G_EXPLICIT = prove
 (`forall c1 c2 a b l. pairin GPAIRS (owned c1 c2 a b l) <=>
     (vector[&457 / &500; &1] IN osq c1 c2 a b l /\ vector[&1; &457 / &500] IN osq c1 c2 a b l) \/
     (vector[&457 / &500; &3] IN osq c1 c2 a b l /\ vector[&1; &1543 / &500] IN osq c1 c2 a b l) \/
     (vector[&1543 / &500; &3] IN osq c1 c2 a b l /\ vector[&3; &1543 / &500] IN osq c1 c2 a b l) \/
     (vector[&1543 / &500; &1] IN osq c1 c2 a b l /\ vector[&3; &457 / &500] IN osq c1 c2 a b l) \/
     (vector[&33 / &20; &33 / &20] IN osq c1 c2 a b l /\ vector[&47 / &20; &33 / &20] IN osq c1 c2 a b l) \/
     (vector[&33 / &20; &47 / &20] IN osq c1 c2 a b l /\ vector[&47 / &20; &47 / &20] IN osq c1 c2 a b l)`,
  REWRITE_TAC[pairin; GPAIRS; EX; owned; IN_ELIM_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MARKER_EXPLICIT; OR_CLAUSES] THEN MESON_TAC[]);;

let FFP_PAIR_CARD = prove
 (`forall c1 c2 a b l P. NPACK c1 c2 a b l
     ==> CARD {G | G IN FFP c1 c2 a b l /\ pairin P G} =
         CARD {i | i < 12 /\ i IN {i | pairin P (owned (c1 i) (c2 i) (a i) (b i) l)}}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{G | G IN FFP c1 c2 a b l /\ pairin P G} =
                IMAGE (\i. owned (c1 i) (c2 i) (a i) (b i) l)
                      {i | i < 12 /\ i IN {i | pairin P (owned (c1 i) (c2 i) (a i) (b i) l)}}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `G:num->bool` THEN
    REWRITE_TAC[FFP; IN_ELIM_THM; IN_IMAGE] THEN
    EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[OWNED_INJ];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < 12}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]]);;

let FFP_BUDGET_F = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> 2 <= CARD {G | G IN FFP c1 c2 a b l /\ pairin FPAIRS G}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FFP_PAIR_CARD] THEN
  MATCH_MP_TAC BUDGET_LEMMA THEN
  EXISTS_TAC `\(i:num) (j:num). fpt j IN osq (c1 i) (c2 i) (a i) (b i) l` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REFUTE_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    REWRITE_TAC[FPT_EXPLICIT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~pairin FPAIRS (owned (c1 (i:num)) (c2 i) (a i) (b i) l)` THEN
    REWRITE_TAC[PAIRIN_F_EXPLICIT] THEN
    MATCH_MP_TAC AVOIDF_FORCES_PAIR THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC_ALL NPACK_SQ) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NPACK_DISJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                          `l:real`; `fpt j`] THEN ASM_REWRITE_TAC[]]);;
let FFP_BUDGET_G = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> 2 <= CARD {G | G IN FFP c1 c2 a b l /\ pairin GPAIRS G}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FFP_PAIR_CARD] THEN
  MATCH_MP_TAC BUDGET_LEMMA THEN
  EXISTS_TAC `\(i:num) (j:num). gpt j IN osq (c1 i) (c2 i) (a i) (b i) l` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REFUTE_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    REWRITE_TAC[GPT_EXPLICIT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~pairin GPAIRS (owned (c1 (i:num)) (c2 i) (a i) (b i) l)` THEN
    REWRITE_TAC[PAIRIN_G_EXPLICIT] THEN
    MATCH_MP_TAC AVOIDG_FORCES_PAIR THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC_ALL NPACK_SQ) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NPACK_DISJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                          `l:real`; `gpt j`] THEN ASM_REWRITE_TAC[]]);;

(* A normalized packing gives a VALIDF family, once the conflict pairs are
   excluded (hull.ml). *)
let NOCONF_FFP = new_definition
 `NOCONF_FFP c1 c2 a b l <=>
    ALL (\(c,d). ~(set_of_list c IN FFP c1 c2 a b l /\ set_of_list d IN FFP c1 c2 a b l)) CONFL`;;

let VALIDF_OF_NPACK = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ NOCONF_FFP c1 c2 a b l
                 ==> VALIDF (FFP c1 c2 a b l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `NOCONF_FFP c1 c2 a b l` THEN
  ASM_SIMP_TAC[VALIDF; NOCONF_FFP; FFP_CARD; FFP_BUDGET_F; FFP_BUDGET_G] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FFP_CLQ]; ASM_MESON_TAC[FFP_DISJ]]);;

let PACKING_CLASSIFIED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ NOCONF_FFP c1 c2 a b l
                 ==> GOALF (FFP c1 c2 a b l)`,
  MESON_TAC[VALIDF_OF_NPACK; FAMILIES_CLASSIFIED]);;
