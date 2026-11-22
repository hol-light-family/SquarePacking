(* ========================================================================= *)
(* Port, layer 6: the singleton seeds (Jatloe: SingletonTriangles,           *)
(* SingletonForcing, CenterLocalization, MarkerCoverGeometry.side_region_hit) *)
(* A square owning exactly marker 0 contains (28/25,1), (87/50,1) and        *)
(* (187/100,19/25).                                                          *)
(* ========================================================================= *)

needs "n12/phase1/auxcover.ml";;
needs "shared/tools/bernstein.ml";;
needs "shared/tools/cover_tac.ml";;

let SPEC5 = [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`];;

let NB088 = ARC_NONNEG `c + s - (c * c * (&457 / &500) + s * s + (&22 / &25) * c * s)`;;
let NB0956 = ARC_NONNEG `c + s - (c * c * (&19 / &25) + s * s + (&239 / &250) * c * s)`;;

(* the bottom wall row of the marker cover, in general direction *)
let BOTTOM_ROW = prove
 (`forall c1 c2 a b l x0 bb.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        x0 <= c1 /\ c1 <= x0 + &1 /\ c2 <= bb /\ bb <= &457 / &500
        ==> vector[x0; bb] IN osq c1 c2 a b l \/ vector[x0 + &1; bb] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MP_TAC(SPECL [`c1 - x0`; `c2:real`; `c:real`; `s:real`; `l:real`; `bb:real`]
         WALL_ROW_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_OSQ] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN BINOP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let SIDE_REGION_HIT = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        c1 <= &457 / &500 /\ &1 <= c2 /\ c2 <= &2
        ==> vector[&457 / &500; &1] IN osq c1 c2 a b l \/
            vector[&457 / &500; &2] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SW_RULE (SPECL [`c2:real`; `c1:real`; `b:real`; `a:real`; `l:real`; `&1`;
                         `&457 / &500`] BOTTOM_ROW)) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `a * a + b * b = &1` THEN
                  RASM_ARITH_TAC; REWRITE_TAC[]]);;

(* the 15 markers other than marker 0 *)
let MARKERS_OUT = `forall j. 0 < j /\ j < 16 ==> ~(marker j IN osq c1 c2 a b l)`;;

let MARKERS_OUT_C = `forall j. 0 < j ==> j < 16 ==> ~(marker j IN osq c1 c2 a b l)`;;

let MARKERS_OUT_TAC =
  FIRST_ASSUM(fun th ->
    let th' = if aconv (concl th) MARKERS_OUT then th
              else if aconv (concl th) MARKERS_OUT_C then REWRITE_RULE[IMP_IMP] th
              else failwith "MARKERS_OUT_TAC" in
    MAP_EVERY (fun j -> ASSUME_TAC(REWRITE_RULE[MARKER_EXPLICIT]
        (MP (SPEC (mk_small_numeral j) th') (EQT_ELIM(NUM_REDUCE_CONV
           (mk_conj(mk_binop `(<):num->num->bool` `0` (mk_small_numeral j),
                    mk_binop `(<):num->num->bool` (mk_small_numeral j) `16`)))))))
        (1--15));;

let ST_REP0TRI0 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&457 / &500",q"&1"),(q"&457 / &500",q"&2"))
  (q"(&125 / &92) * c1 + (&0) * c2 + (-- &457 / &368)",
   q"((-- &175 / &368)) * c1 + (-- &1) * c2 + &17919 / &7360",
   q"((-- &325 / &368)) * c1 + (&1) * c2 + (-- &1419 / &7360)");;
let ST_REP0TRI1 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&457 / &500",q"&2"),(q"&33 / &20",q"&47 / &20"))
  (q"(&125 / &184) * c1 + ((-- &10 / &7)) * c2 + &11521 / &5152",
   q"((-- &125 / &92)) * c1 + (&0) * c2 + &825 / &368",
   q"(&125 / &184) * c1 + (&10 / &7) * c2 + (-- &17919 / &5152)");;
let ST_REP0TRI2 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&33 / &20",q"&47 / &20"),(q"&47 / &20",q"&33 / &20"))
  (q"((-- &10 / &7)) * c1 + ((-- &10 / &7)) * c2 + &40 / &7",
   q"(&0) * c1 + (&10 / &7) * c2 + (-- &33 / &14)",
   q"(&10 / &7) * c1 + (&0) * c2 + (-- &33 / &14)");;
let ST_REP0TRI3 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&47 / &20",q"&33 / &20"),(q"&2",q"&457 / &500"))
  (q"((-- &10 / &7)) * c1 + (&125 / &184) * c2 + &11521 / &5152",
   q"(&10 / &7) * c1 + (&125 / &184) * c2 + (-- &17919 / &5152)",
   q"(&0) * c1 + ((-- &125 / &92)) * c2 + &825 / &368");;
let ST_REP0TRI4 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&2",q"&457 / &500"),(q"&28 / &25",q"&1"))
  (q"(&4300 / &30879) * c1 + (&44000 / &30879) * c2 + (-- &5424 / &3431)",
   q"(&32500 / &30879) * c1 + ((-- &26500 / &30879)) * c2 + (-- &1100 / &3431)",
   q"((-- &36800 / &30879)) * c1 + ((-- &17500 / &30879)) * c2 + &9955 / &3431");;
let ST_REP0TRI5 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&28 / &25",q"&1"),(q"&457 / &500",q"&1"))
  (q"(&0) * c1 + (&20 / &13) * c2 + (-- &20 / &13)",
   q"(&500 / &103) * c1 + ((-- &7360 / &1339)) * c2 + &1419 / &1339",
   q"((-- &500 / &103)) * c1 + (&5300 / &1339) * c2 + &1980 / &1339");;
let ST_REP1TRI0 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&2",q"&457 / &500"),(q"&87 / &50",q"&1"))
  (q"(&4300 / &8063) * c1 + (&13000 / &8063) * c2 + (-- &1862 / &733)",
   q"(&32500 / &8063) * c1 + (&4500 / &8063) * c2 + (-- &5550 / &733)",
   q"((-- &36800 / &8063)) * c1 + ((-- &17500 / &8063)) * c2 + &8145 / &733");;
let ST_REP1TRI5 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&87 / &50",q"&1"),(q"&457 / &500",q"&1"))
  (q"(&0) * c1 + (&20 / &13) * c2 + (-- &20 / &13)",
   q"(&500 / &413) * c1 + ((-- &7360 / &5369)) * c2 + &1419 / &5369",
   q"((-- &500 / &413)) * c1 + ((-- &900 / &5369)) * c2 + &12210 / &5369");;
let ST_REP2TRI0 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&2",q"&457 / &500"),(q"&187 / &100",q"&19 / &25"))
  (q"((-- &7700 / &7479)) * c1 + (&6500 / &7479) * c2 + &1051 / &831",
   q"(&44500 / &7479) * c1 + (&11000 / &7479) * c2 + (-- &10175 / &831)",
   q"((-- &36800 / &7479)) * c1 + ((-- &17500 / &7479)) * c2 + &9955 / &831");;
let ST_REP2TRI5 = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&187 / &100",q"&19 / &25"),(q"&457 / &500",q"&1"))
  (q"(&6000 / &19951) * c1 + (&23900 / &19951) * c2 + (-- &29384 / &19951)",
   q"(&16250 / &19951) * c1 + ((-- &18400 / &19951)) * c2 + &7095 / &39902",
   q"((-- &22250 / &19951)) * c1 + ((-- &5500 / &19951)) * c2 + &91575 / &39902");;

let UPPER4 = [ST_REP0TRI0; ST_REP0TRI1; ST_REP0TRI2; ST_REP0TRI3];;

let REPLACEMENT_TAC tris =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MARKERS_OUT_TAC THEN COVER_TAC SPEC5 (UPPER4 @ tris);;

let REPLACEMENT0 = prove
 (mk_forall(`c1:real`, mk_forall(`c2:real`, mk_forall(`a:real`, mk_forall(`b:real`, mk_forall(`l:real`,
   mk_imp(list_mk_conj [`&1 < l`; `a * a + b * b = &1`; MARKERS_OUT;
     `&457 / &500 <= c1`; `c1 <= &2`; `&1 <= c2`; `c2 <= &2`],
     `vector[&28 / &25; &1] IN osq c1 c2 a b l`)))))),
  REPLACEMENT_TAC [ST_REP0TRI4; ST_REP0TRI5]);;

let REPLACEMENT1 = prove
 (mk_forall(`c1:real`, mk_forall(`c2:real`, mk_forall(`a:real`, mk_forall(`b:real`, mk_forall(`l:real`,
   mk_imp(list_mk_conj [`&1 < l`; `a * a + b * b = &1`; MARKERS_OUT;
     `&457 / &500 <= c1`; `c1 <= &2`; `&1 <= c2`; `c2 <= &2`],
     `vector[&87 / &50; &1] IN osq c1 c2 a b l`)))))),
  REPLACEMENT_TAC [ST_REP1TRI0; ST_REP1TRI5]);;

let REPLACEMENT2 = prove
 (mk_forall(`c1:real`, mk_forall(`c2:real`, mk_forall(`a:real`, mk_forall(`b:real`, mk_forall(`l:real`,
   mk_imp(list_mk_conj [`&1 < l`; `a * a + b * b = &1`; MARKERS_OUT;
     `&457 / &500 <= c1`; `c1 <= &2`; `&1 <= c2`; `c2 <= &2`],
     `vector[&187 / &100; &19 / &25] IN osq c1 c2 a b l`)))))),
  REPLACEMENT_TAC [ST_REP2TRI0; ST_REP2TRI5]);;

let REPLACEMENT2R = prove
 (mk_forall(`c1:real`, mk_forall(`c2:real`, mk_forall(`a:real`, mk_forall(`b:real`, mk_forall(`l:real`,
   mk_imp(list_mk_conj [`&1 < l`; `a * a + b * b = &1`; MARKERS_OUT;
     `&187 / &100 <= c1`; `c1 <= &2`; `&457 / &500 <= c2`; `c2 <= &2`],
     `vector[&187 / &100; &19 / &25] IN osq c1 c2 a b l`)))))),
  REPLACEMENT_TAC [ST_REP2TRI0; ST_REP2TRI5]);;

let SINGLETON_HYPS = list_mk_conj [`&1 < l`; `l <= &1001 / &1000`; `a * a + b * b = &1`;
   `owalls c1 c2 a b l`; `vector[&1; &457 / &500] IN osq c1 c2 a b l`; MARKERS_OUT];;

let mk_singleton_goal p =
  list_mk_forall(SPEC5, mk_imp(SINGLETON_HYPS,
    mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, p), `osq c1 c2 a b l`)));;

let NB_TAC nb =
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`c:real`; `s:real`] nb) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;;

let NBS_TAC =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NB_SMALL THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV;;

(* apply a two-point lemma; the antecedent is closed by arithmetic, except a
   universally quantified orientation bound, closed by ntac *)
let SEG_TAC lemma args ntac =
  MP_TAC(SPECL (SPEC5 @ args) lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC; RASM_ARITH_TAC; ntac];
    ASM_REWRITE_TAC[]];;

let SINGLETON_TAC px d wallL wallR triL triR =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL SPEC5 CORNER_OWNER_CENTER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MARKERS_OUT_TAC THEN
  ASM_CASES_TAC `c1 <= &457 / &500` THENL
   [ASM_CASES_TAC `c2 <= &1` THENL
     [MP_TAC(SPECL (SPEC5 @ [`&457 / &500`]) CORNER_H) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      MP_TAC(SPECL SPEC5 SIDE_REGION_HIT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_CASES_TAC (mk_binop `(<=):real->real->bool` `c1:real` px) THENL
   [ASM_CASES_TAC `c2 <= &1` THENL
     [wallL; MP_TAC(SPECL SPEC5 triL) THEN
             ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; REWRITE_TAC[]]];
    ASM_CASES_TAC (mk_binop `(<=):real->real->bool` `c2:real` d) THENL
     [wallR; MP_TAC(SPECL SPEC5 triR) THEN
             ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; REWRITE_TAC[]]]];;

let SINGLETON_112 = prove
 (mk_singleton_goal `vector[&28 / &25; &1]:real^2`,
  SINGLETON_TAC `&28 / &25` `&1`
   (SEG_TAC BOTTOM_SEGMENT [`&457 / &500`; `&28 / &25`; `&1`] ALL_TAC)
   (SEG_TAC GEN_SEGMENT_DESC [`&28 / &25`; `&2`; `&1`; `&457 / &500`] (NB_TAC NB088))
   REPLACEMENT0 REPLACEMENT0);;

let SINGLETON_174 = prove
 (mk_singleton_goal `vector[&87 / &50; &1]:real^2`,
  SINGLETON_TAC `&87 / &50` `&1`
   (SEG_TAC BOTTOM_SEGMENT [`&457 / &500`; `&87 / &50`; `&1`] ALL_TAC)
   (SEG_TAC GEN_SEGMENT_DESC [`&87 / &50`; `&2`; `&1`; `&457 / &500`] NBS_TAC)
   REPLACEMENT1 REPLACEMENT1);;

let SINGLETON_187 = prove
 (mk_singleton_goal `vector[&187 / &100; &19 / &25]:real^2`,
  SINGLETON_TAC `&187 / &100` `&457 / &500`
   (SEG_TAC GEN_SEGMENT_DESC [`&457 / &500`; `&187 / &100`; `&1`; `&19 / &25`] (NB_TAC NB0956))
   (SEG_TAC GEN_SEGMENT_HIT [`&187 / &100`; `&2`; `&19 / &25`; `&457 / &500`] NBS_TAC)
   REPLACEMENT2 REPLACEMENT2R);;
