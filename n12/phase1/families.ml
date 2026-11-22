(* ========================================================================= *)
(* Port, layers 3-5: the finite classification of marker families.          *)
(* A packing gives 12 pairwise disjoint marker groups from the 103 cliques;  *)
(* a marker-ordered search (with the counting and pair-budget prunings)      *)
(* lists every such family that also passes the conflict and budget rules.   *)
(* ========================================================================= *)

needs "n12/phase1/groups.ml";;
loadt "n12/phase1/families_data.ml";;

let FPAIRS = new_definition
 `FPAIRS = [0,1; 2,3; 4,5; 6,7; 8,11; 9,10]`;;
let GPAIRS = new_definition
 `GPAIRS = [0,1; 2,3; 4,5; 6,7; 8,9; 10,11]`;;

let haspair = new_definition
 `haspair (P:(num#num)list) (c:num list) <=> EX (\(a,b). MEM a c /\ MEM b c) P`;;

let rangelist = define
 `(rangelist k 0 = []) /\ (rangelist k (SUC n) = CONS k (rangelist (SUC k) n))`;;

let freeN = new_definition
 `freeN k used = LENGTH (FILTER (\j. ~MEM j used) (rangelist k (16 - k)))`;;

let avail = new_definition
 `avail (P:(num#num)list) k used =
    LENGTH (FILTER (\(a,b). k <= a /\ k <= b /\ ~MEM a used /\ ~MEM b used) P)`;;

let prune = new_definition
 `prune k used (ch:(num list)list) <=>
    LENGTH ch + freeN k used < 12 \/
    LENGTH (FILTER (haspair FPAIRS) ch) + avail FPAIRS k used < 2 \/
    LENGTH (FILTER (haspair GPAIRS) ch) + avail GPAIRS k used < 2`;;

let fin_ok = new_definition
 `fin_ok (ch:(num list)list) <=>
    LENGTH ch = 12 /\ 2 <= LENGTH (FILTER (haspair FPAIRS) ch) /\
    2 <= LENGTH (FILTER (haspair GPAIRS) ch)`;;

let noconf = new_definition
 `noconf (c:num list) ch <=> ALL (\d. ~MEM (c,d) CONFL /\ ~MEM (d,c) CONFL) ch`;;

(* ------------------------------------------------------------------------- *)
(* Semantic families and the search invariant.                               *)
(* ------------------------------------------------------------------------- *)

let pairin = new_definition
 `pairin (P:(num#num)list) (G:num->bool) <=> EX (\(a,b). a IN G /\ b IN G) P`;;

let VALIDF = new_definition
 `VALIDF (FF:(num->bool)->bool) <=>
    FINITE FF /\ CARD FF = 12 /\
    (forall G. G IN FF ==> exists c. MEM c CLQ /\ G = set_of_list c) /\
    (forall G H. G IN FF /\ H IN FF /\ ~(G = H) ==> DISJOINT G H) /\
    ALL (\(c,d). ~(set_of_list c IN FF /\ set_of_list d IN FF)) CONFL /\
    2 <= CARD {G | G IN FF /\ pairin FPAIRS G} /\
    2 <= CARD {G | G IN FF /\ pairin GPAIRS G}`;;

let FBEL = new_definition
 `FBEL (FF:(num->bool)->bool) k = {G | G IN FF /\ exists j. j < k /\ j IN G}`;;

let FLATL = new_definition
 `FLATL (L:(num list)list) = ITLIST APPEND L []`;;

let INVF = new_definition
 `INVF FF k (L:(num list)list) <=>
    FBEL FF k = set_of_list (MAP set_of_list L) /\
    LENGTH L = CARD (FBEL FF k) /\
    ALL (\c. MEM c CLQ) L`;;

let CLQ_PROPS = prove
 (`ALL (\c. sorted_lt c /\ ~(c = []) /\ ALL (\x. x < 16) c) CLQ`,
  REWRITE_TAC[CLQ; ALL; sorted_lt; HD; NOT_CONS_NIL] THEN CONV_TAC NUM_REDUCE_CONV);;

let CLQ_PROP = prove
 (`forall c. MEM c CLQ ==> sorted_lt c /\ ~(c = []) /\ (forall x. MEM x c ==> x < 16)`,
  GEN_TAC THEN MP_TAC CLQ_PROPS THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let SORTED_HD_LE = prove
 (`forall c x. sorted_lt c /\ MEM x c ==> HD c <= x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INCR_ALL_LT) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MEM_FLATL = prove
 (`forall L x. MEM x (FLATL L) <=> exists c. MEM c L /\ MEM x c`,
  REWRITE_TAC[FLATL] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; MEM; MEM_APPEND] THEN MESON_TAC[]);;

let INVF_MEM = prove
 (`forall FF k L G. INVF FF k L ==> (G IN FBEL FF k <=> exists c. MEM c L /\ G = set_of_list c)`,
  REWRITE_TAC[INVF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

let FBEL_SUBSET = prove
 (`forall FF k G. G IN FBEL FF k ==> G IN FF`,
  REWRITE_TAC[FBEL; IN_ELIM_THM] THEN MESON_TAC[]);;

let INVF_0 = prove
 (`forall FF. INVF FF 0 []`,
  REWRITE_TAC[INVF; FBEL; LT; MAP; set_of_list; ALL; LENGTH] THEN
  REWRITE_TAC[EMPTY_GSPEC; CARD_CLAUSES]);;

let VALIDF_GROUP = prove
 (`forall FF G. VALIDF FF /\ G IN FF
          ==> exists c. MEM c CLQ /\ G = set_of_list c /\ sorted_lt c /\ ~(c = []) /\
                  (forall x. MEM x c ==> x < 16)`,
  REWRITE_TAC[VALIDF] THEN MESON_TAC[CLQ_PROP]);;

let VALIDF_DISJ = prove
 (`forall FF G H x. VALIDF FF /\ G IN FF /\ H IN FF /\ x IN G /\ x IN H ==> G = H`,
  REWRITE_TAC[VALIDF; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let INVF_USED = prove
 (`forall FF k L. VALIDF FF /\ INVF FF k L /\ MEM k (FLATL L) ==> INVF FF (SUC k) L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FBEL FF (SUC k) = FBEL FF k` (fun th -> ASM_MESON_TAC[th; INVF]) THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `G:num->bool` THEN
  REWRITE_TAC[FBEL; IN_ELIM_THM; LT] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  UNDISCH_TAC `MEM k (FLATL L)` THEN REWRITE_TAC[MEM_FLATL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `set_of_list (c:num list) IN FBEL FF k` ASSUME_TAC THENL
   [ASM_MESON_TAC[INVF_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `G = set_of_list (c:num list)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VALIDF_DISJ THEN MAP_EVERY EXISTS_TAC [`FF:(num->bool)->bool`; `k:num`] THEN
    ASM_MESON_TAC[FBEL_SUBSET; IN_SET_OF_LIST];
    ALL_TAC] THEN
  UNDISCH_TAC `set_of_list (c:num list) IN FBEL FF k` THEN REWRITE_TAC[FBEL; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let FINITE_FBEL = prove
 (`forall FF k. FINITE FF ==> FINITE (FBEL FF k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `FF:(num->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN MESON_TAC[FBEL_SUBSET]);;

let INVF_STEP = prove
 (`forall FF k L. VALIDF FF /\ INVF FF k L
     ==> INVF FF (SUC k) L \/
         exists c. MEM c CLQ /\ HD c = k /\ set_of_list c IN FF /\
             ~(set_of_list c IN FBEL FF k) /\ INVF FF (SUC k) (CONS c L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `exists G. G IN FF /\ k IN G /\ ~(G IN FBEL FF k)` THENL
   [DISJ2_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `G0:num->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`FF:(num->bool)->bool`; `G0:num->bool`] VALIDF_GROUP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:num list` THEN
    SUBGOAL_THEN `HD (c:num list) = k` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `(h:num) <= k /\ ~(h < k) ==> h = k`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC SORTED_HD_LE THEN ASM_MESON_TAC[IN_SET_OF_LIST];
        DISCH_TAC THEN UNDISCH_TAC `~(G0 IN FBEL FF k)` THEN
        REWRITE_TAC[FBEL; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `HD c:num` THEN ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
        UNDISCH_TAC `~(c:num list = [])` THEN SPEC_TAC(`c:num list`,`c:num list`) THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC[HD; MEM]];
      ALL_TAC] THEN
    UNDISCH_THEN `G0 = set_of_list (c:num list)` SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `FBEL FF (SUC k) = set_of_list (c:num list) INSERT FBEL FF k` ASSUME_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INSERT] THEN
      X_GEN_TAC `G:num->bool` THEN
      REWRITE_TAC[FBEL; IN_ELIM_THM; LT] THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
        ASM_CASES_TAC `exists j. j < k /\ j IN (G:num->bool)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC VALIDF_DISJ THEN
        MAP_EVERY EXISTS_TAC [`FF:(num->bool)->bool`; `k:num`] THEN
        ASM_MESON_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
        EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (FBEL FF k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_FBEL; VALIDF]; ALL_TAC] THEN
    SUBGOAL_THEN `CARD (FBEL FF (SUC k)) = SUC (CARD (FBEL FF k))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES]; ALL_TAC] THEN
    UNDISCH_TAC `INVF FF k L` THEN REWRITE_TAC[INVF] THEN STRIP_TAC THEN
    REWRITE_TAC[MAP; set_of_list; ALL; LENGTH] THEN
    ASM_REWRITE_TAC[];
    DISJ1_TAC THEN
    SUBGOAL_THEN `FBEL FF (SUC k) = FBEL FF k`
     (fun th -> UNDISCH_TAC `INVF FF k L` THEN REWRITE_TAC[INVF; th]) THEN
    REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `G:num->bool` THEN
    REWRITE_TAC[FBEL; IN_ELIM_THM; LT] THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `G:num->bool` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[FBEL; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Prunings and the leaf.                                                    *)
(* ------------------------------------------------------------------------- *)

let INVF_FLATL = prove
 (`forall FF k L x. INVF FF k L /\ MEM x (FLATL L)
              ==> exists G. G IN FBEL FF k /\ x IN G`,
  REWRITE_TAC[MEM_FLATL] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `set_of_list (c:num list)` THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN ASM_MESON_TAC[INVF_MEM]);;

let P_DISJ = prove
 (`forall FF k L c x. VALIDF FF /\ INVF FF k L /\ set_of_list c IN FF /\
                ~(set_of_list c IN FBEL FF k) /\ MEM x c /\ MEM x (FLATL L) ==> false`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`; `L:(num list)list`; `x:num`] INVF_FLATL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `G:num->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `set_of_list (c:num list) = G` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC VALIDF_DISJ THEN
  MAP_EVERY EXISTS_TAC [`FF:(num->bool)->bool`; `x:num`] THEN
  ASM_MESON_TAC[FBEL_SUBSET; IN_SET_OF_LIST]);;

let P_CONF = prove
 (`forall FF k L c d. VALIDF FF /\ INVF FF k L /\ set_of_list c IN FF /\ MEM d L /\
                (MEM (c,d) CONFL \/ MEM (d,c) CONFL) ==> false`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `set_of_list (d:num list) IN FF` ASSUME_TAC THENL
   [ASM_MESON_TAC[INVF_MEM; FBEL_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `VALIDF FF` THEN REWRITE_TAC[VALIDF; GSYM ALL_MEM] THEN
  STRIP_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(c:num list),(d:num list)`);
    FIRST_X_ASSUM(MP_TAC o SPEC `(d:num list),(c:num list)`)] THEN
  ASM_REWRITE_TAC[]);;

let P_TOOMANY = prove
 (`forall FF k L. VALIDF FF /\ INVF FF k L /\ 12 < LENGTH (L:(num list)list) ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INVF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD (FBEL FF k) <= CARD (FF:(num->bool)->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[SUBSET] THEN
    ASM_MESON_TAC[FBEL_SUBSET; VALIDF];
    ASM_MESON_TAC[VALIDF; ARITH_RULE `12 < n ==> ~(n <= 12)`]]);;

let INVF_LEAF = prove
 (`forall FF L. VALIDF FF /\ INVF FF 16 L ==> FF = set_of_list (MAP set_of_list L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FBEL FF 16 = FF` (fun th -> ASM_MESON_TAC[th; INVF]) THEN
  REWRITE_TAC[EXTENSION; FBEL; IN_ELIM_THM] THEN X_GEN_TAC `G:num->bool` THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`FF:(num->bool)->bool`; `G:num->bool`] VALIDF_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `HD c:num` THEN ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
  SUBGOAL_THEN `MEM (HD c) (c:num list)` (fun th -> ASM_MESON_TAC[th]) THEN
  UNDISCH_TAC `~(c:num list = [])` THEN SPEC_TAC(`c:num list`,`c:num list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; MEM]);;

let MEM_RANGELIST = prove
 (`forall n k j. MEM j (rangelist k n) <=> k <= j /\ j < k + n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[rangelist; MEM] THEN ARITH_TAC);;

let REST_ELEM = prove
 (`forall FF k L G x. VALIDF FF /\ INVF FF k L /\ G IN FF /\ ~(G IN FBEL FF k) /\ x IN G
                ==> k <= x /\ x < 16 /\ ~MEM x (FLATL L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(G IN FBEL FF k)` THEN REWRITE_TAC[FBEL; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[VALIDF_GROUP; IN_SET_OF_LIST];
    DISCH_TAC THEN
    MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`; `L:(num list)list`; `x:num`]
                 INVF_FLATL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `H:num->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `G:num->bool = H` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC VALIDF_DISJ THEN
    MAP_EVERY EXISTS_TAC [`FF:(num->bool)->bool`; `x:num`] THEN
    ASM_MESON_TAC[FBEL_SUBSET]]);;

let CARD_REST = prove
 (`forall FF k L. VALIDF FF /\ INVF FF k L
            ==> CARD {G | G IN FF /\ ~(G IN FBEL FF k)} + LENGTH L = 12`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (L:(num list)list) = CARD (FBEL FF k)` SUBST1_TAC THENL
   [ASM_MESON_TAC[INVF]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (FF:(num->bool)->bool) = 12 /\ FINITE FF` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[VALIDF]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (FBEL FF k) + CARD {G | G IN FF /\ ~(G IN FBEL FF k)} =
                CARD (FF:(num->bool)->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`] FBEL_SUBSET) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let CARD_INJ_LE = prove
 (`forall (f:A->B) s t. FINITE s /\ FINITE t /\ (forall x. x IN s ==> f x IN t) /\
                  (forall x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
                  ==> CARD s <= CARD t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `s:A->bool`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P_COUNT = prove
 (`forall FF k L. VALIDF FF /\ INVF FF k L /\ k <= 16 /\ LENGTH L + freeN k (FLATL L) < 12
            ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`; `L:(num list)list`] CARD_REST) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `CARD {G | G IN FF /\ ~(G IN FBEL FF k)} <=
    CARD (set_of_list (FILTER (\j. ~MEM j (FLATL L)) (rangelist k (16 - k))))`
  MP_TAC THENL
   [MATCH_MP_TAC CARD_INJ_LE THEN EXISTS_TAC `\G:num->bool. @x:num. x IN G` THEN
    REWRITE_TAC[FINITE_SET_OF_LIST; IN_SET_OF_LIST; MEM_FILTER; MEM_RANGELIST;
                IN_ELIM_THM] THEN
    SUBGOAL_THEN `forall G. G IN FF ==> (@x:num. x IN G) IN G` ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN CONV_TAC SELECT_CONV THEN
      MP_TAC(SPECL [`FF:(num->bool)->bool`; `G:num->bool`] VALIDF_GROUP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `HD c:num` THEN
      ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
      UNDISCH_TAC `~(c:num list = [])` THEN SPEC_TAC(`c:num list`,`c:num list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; MEM];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `FF:(num->bool)->bool` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[VALIDF];
      X_GEN_TAC `G:num->bool` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`; `L:(num list)list`; `G:num->bool`;
                    `@x:num. x IN G`] REST_ELEM) THEN
      ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`G:num->bool`; `H:num->bool`] THEN STRIP_TAC THEN
      MATCH_MP_TAC VALIDF_DISJ THEN
      MAP_EVERY EXISTS_TAC [`FF:(num->bool)->bool`; `@x:num. x IN G`] THEN
      ASM_MESON_TAC[]];
    MP_TAC(ISPEC `FILTER (\j. ~MEM j (FLATL L)) (rangelist k (16 - k))`
                 CARD_SET_OF_LIST_LE) THEN
    REWRITE_TAC[GSYM freeN] THEN
    UNDISCH_TAC `LENGTH (L:(num list)list) + freeN k (FLATL L) < 12` THEN
    ABBREV_TAC `fr = freeN k (FLATL L)` THEN
    ABBREV_TAC `aa = CARD (set_of_list (FILTER (\j. ~MEM j (FLATL L)) (rangelist k (16 - k))))` THEN
    ABBREV_TAC `rr = CARD {G | G IN FF /\ ~(G IN FBEL FF k)}` THEN
    ARITH_TAC]);;

let PAIRIN_ALT = prove
 (`forall P G. pairin P G <=> exists p. MEM p P /\ FST p IN G /\ SND p IN G`,
  REWRITE_TAC[pairin; GSYM EX_MEM; EXISTS_PAIR_THM; FST; SND] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

let PAIRIN_SET = prove
 (`forall P c. pairin P (set_of_list c) <=> haspair P c`,
  REWRITE_TAC[pairin; haspair; IN_SET_OF_LIST]);;

let MEM_AVAIL = prove
 (`forall (P:(num#num)list) (k:num) (used:num list) p.
       MEM p (FILTER (\(a,b). k <= a /\ k <= b /\ ~MEM a used /\ ~MEM b used) P)
                <=> MEM p P /\ k <= FST p /\ k <= SND p /\ ~MEM (FST p) used /\
                    ~MEM (SND p) used`,
  REWRITE_TAC[MEM_FILTER; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN MESON_TAC[]);;

let P_BUDGET = prove
 (`forall P FF k L. VALIDF FF /\ INVF FF k L /\ 2 <= CARD {G | G IN FF /\ pairin P G} /\
              LENGTH (FILTER (haspair P) L) + avail P k (FLATL L) < 2 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (FF:(num->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[VALIDF]; ALL_TAC] THEN
  ABBREV_TAC `A2 = {G | G IN FF /\ ~(G IN FBEL FF k) /\ pairin P G}` THEN
  ABBREV_TAC `B1 = set_of_list (MAP set_of_list (FILTER (haspair P) L))` THEN
  SUBGOAL_THEN `CARD {G | G IN FF /\ pairin P G} <= CARD (B1:(num->bool)->bool) + CARD (A2:(num->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD ((B1:(num->bool)->bool) UNION A2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["A2"; "B1"] THEN
        REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_SET_OF_LIST; MEM_MAP; MEM_FILTER] THEN
        X_GEN_TAC `G:num->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(G:num->bool) IN FBEL FF k` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] INVF_MEM)) THEN
        DISCH_THEN(MP_TAC o SPEC `G:num->bool`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN EXISTS_TAC `c:num list` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[PAIRIN_SET];
        MATCH_MP_TAC FINITE_UNION_IMP THEN
        EXPAND_TAC "B1" THEN REWRITE_TAC[FINITE_SET_OF_LIST] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `FF:(num->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "A2" THEN SET_TAC[]];
      MATCH_MP_TAC CARD_UNION_LE THEN EXPAND_TAC "B1" THEN
      REWRITE_TAC[FINITE_SET_OF_LIST] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `FF:(num->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "A2" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (B1:(num->bool)->bool) <= LENGTH (FILTER (haspair P) L)` ASSUME_TAC
  THENL
   [EXPAND_TAC "B1" THEN
    W(fun (_,w) -> MP_TAC(ISPEC (rand(rand(lhand w))) CARD_SET_OF_LIST_LE)) THEN
    REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (A2:(num->bool)->bool) <= avail P k (FLATL L)` ASSUME_TAC THENL
   [REWRITE_TAC[avail] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (set_of_list (FILTER (\(a,b). k <= a /\ k <= b /\
                    ~MEM a (FLATL L) /\ ~MEM b (FLATL L)) (P:(num#num)list)))` THEN
    REWRITE_TAC[CARD_SET_OF_LIST_LE] THEN
    MATCH_MP_TAC CARD_INJ_LE THEN
    EXISTS_TAC `\G:num->bool. @p:num#num. MEM p P /\ FST p IN G /\ SND p IN G` THEN
    REWRITE_TAC[FINITE_SET_OF_LIST; IN_SET_OF_LIST; MEM_AVAIL] THEN
    SUBGOAL_THEN `forall G. G IN A2 ==> (\p:num#num. MEM p P /\ FST p IN G /\ SND p IN G)
                                   (@p:num#num. MEM p P /\ FST p IN G /\ SND p IN G)`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "A2" THEN REWRITE_TAC[IN_ELIM_THM; PAIRIN_ALT] THEN
      STRIP_TAC THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(BETA_RULE) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `FF:(num->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "A2" THEN SET_TAC[];
      X_GEN_TAC `G:num->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `G:num->bool`) THEN ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `q = @p:num#num. MEM p P /\ FST p IN G /\ SND p IN G` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(G:num->bool) IN A2` THEN EXPAND_TAC "A2" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`; `L:(num list)list`; `G:num->bool`;
                    `FST(q:num#num)`] REST_ELEM) THEN
      MP_TAC(SPECL [`FF:(num->bool)->bool`; `k:num`; `L:(num list)list`; `G:num->bool`;
                    `SND(q:num#num)`] REST_ELEM) THEN
      ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`P:(num#num)list`; `k:num`; `FLATL L`; `q:num#num`] MEM_AVAIL) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`G:num->bool`; `H:num->bool`] THEN STRIP_TAC THEN
      MATCH_MP_TAC VALIDF_DISJ THEN
      MAP_EVERY EXISTS_TAC [`FF:(num->bool)->bool`;
        `FST(@p:num#num. MEM p P /\ FST p IN G /\ SND p IN G)`] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(G:num->bool) IN FF /\ H IN FF` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(G:num->bool) IN A2` THEN UNDISCH_TAC `(H:num->bool) IN A2` THEN
        EXPAND_TAC "A2" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `2 <= CARD {G | G IN FF /\ pairin P G}` THEN
  UNDISCH_TAC `LENGTH (FILTER (haspair P) (L:(num list)list)) + avail P k (FLATL L) < 2` THEN
  UNDISCH_TAC `CARD {G | G IN FF /\ pairin P G} <= CARD (B1:(num->bool)->bool) + CARD (A2:(num->bool)->bool)` THEN
  UNDISCH_TAC `CARD (B1:(num->bool)->bool) <= LENGTH (FILTER (haspair P) L)` THEN
  UNDISCH_TAC `CARD (A2:(num->bool)->bool) <= avail P k (FLATL L)` THEN
  ABBREV_TAC `x1 = CARD {G | G IN FF /\ pairin P G}` THEN
  ABBREV_TAC `x2 = CARD (B1:(num->bool)->bool)` THEN
  ABBREV_TAC `x3 = CARD (A2:(num->bool)->bool)` THEN
  ABBREV_TAC `x4 = LENGTH (FILTER (haspair P) (L:(num list)list))` THEN
  ABBREV_TAC `x5 = avail P k (FLATL L)` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The target: up to a symmetry, the family of masks is one of the 577 rows. *)
(* ------------------------------------------------------------------------- *)

loadt "n12/phase1/rows_data.ml";;

let dperm = new_definition
 `dperm t k = EL k (EL t MPERMS)`;;

let GOALF = new_definition
 `GOALF (FF:(num->bool)->bool) <=>
    exists t r. t < 8 /\ MEM r ROWS /\
          IMAGE (\G. binarysum (IMAGE (dperm t) G)) FF = set_of_list r`;;

let BINARYSUM_DISTINCT_LIST = prove
 (`forall l. PAIRWISE (\x y. ~(x = y)) l
       ==> binarysum (set_of_list l) = ITLIST (\k a. 2 EXP k + a) l 0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[set_of_list; ITLIST; binarysum; NSUM_CLAUSES] THEN
  REWRITE_TAC[PAIRWISE] THEN STRIP_TAC THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_SET_OF_LIST] THEN
  SUBGOAL_THEN `~((h:num) IN set_of_list t)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `ALL (\y. ~(h:num = y)) t` THEN
    REWRITE_TAC[GSYM ALL_MEM; IN_SET_OF_LIST] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM binarysum] THEN AP_TERM_TAC THEN ASM_SIMP_TAC[]);;

let SET_OF_LIST_EQ_ALL = prove
 (`forall l1 l2:A list. ALL (\x. MEM x l2) l1 /\ ALL (\x. MEM x l1) l2
                  ==> set_of_list l1 = set_of_list l2`,
  REWRITE_TAC[GSYM ALL_MEM; EXTENSION; IN_SET_OF_LIST] THEN MESON_TAC[]);;

let LEAF_GOAL = prove
 (`forall FF L t r.
      VALIDF FF /\ INVF FF 16 L /\ t < 8 /\ MEM r ROWS /\
      ALL (\c. PAIRWISE (\x y. ~(x = y)) (MAP (dperm t) c)) L /\
      set_of_list (MAP (\c. ITLIST (\k a. 2 EXP k + a) (MAP (dperm t) c) 0) L) =
      set_of_list r
      ==> GOALF FF`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GOALF] THEN
  MAP_EVERY EXISTS_TAC [`t:num`; `r:num list`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INVF_LEAF o CONJ (ASSUME `VALIDF FF`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     can (find_term ((=) `r:num list`)) (concl th))) THEN
  REWRITE_TAC[GSYM SET_OF_LIST_MAP; GSYM MAP_o; o_DEF] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  UNDISCH_TAC `ALL (\c. PAIRWISE (\x y. ~(x = y)) (MAP (dperm t) c)) L` THEN
  MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC `c:num list` THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM SET_OF_LIST_MAP] THEN
  ASM_SIMP_TAC[BINARYSUM_DISTINCT_LIST]);;
