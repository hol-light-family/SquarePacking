(* ========================================================================= *)
(* Port, layer 7: the 37 rational hull-conflict certificates (Jatloe:        *)
(* Seeds, HullData, HullBridge, Convex).  Squares owning the two groups of a *)
(* conflicting pair always share an interior point, so no packing has both.  *)
(* ========================================================================= *)

needs "n12/phase1/singleton.ml";;
needs "n12/phase1/bridge.ml";;
loadt "n12/phase1/hull_data.ml";;

let OSQ_SEG = prove
 (`forall x0 y0 x1 y1 t c1 c2 a b l.
        vector[x0; y0] IN osq c1 c2 a b l /\ vector[x1; y1] IN osq c1 c2 a b l /\
        &0 <= t /\ t <= &1
        ==> vector[(&1 - t) * x0 + t * x1; (&1 - t) * y0 + t * y1] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN STRIP_TAC THEN
  ABBREV_TAC `u0 = (x0 - c1) * a + (y0 - c2) * b` THEN
  ABBREV_TAC `v0 = (y0 - c2) * a - (x0 - c1) * b` THEN
  ABBREV_TAC `u1 = (x1 - c1) * a + (y1 - c2) * b` THEN
  ABBREV_TAC `v1 = (y1 - c2) * a - (x1 - c1) * b` THEN
  SUBGOAL_THEN
   `(((&1 - t) * x0 + t * x1) - c1) * a + (((&1 - t) * y0 + t * y1) - c2) * b =
    (&1 - t) * u0 + t * u1 /\
    (((&1 - t) * y0 + t * y1) - c2) * a - (((&1 - t) * x0 + t * x1) - c1) * b =
    (&1 - t) * v0 + t * v1` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["u0"; "v0"; "u1"; "v1"] THEN CONJ_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = &1` THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `t < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN NLIN_TAC []]);;

(* ------------------------------------------------------------------------- *)
(* Singleton seeds for each of the eight corner markers.                     *)
(* ------------------------------------------------------------------------- *)

let MARKER_PTS = map (fun k -> let x,y = marker_xy k in
  mk_comb(`vector:(real)list->real^2`, mk_list([x;y],`:real`))) (0--15);;

let mem_osq p = mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, p), `osq c1 c2 a b l`);;

(* explicit form: marker 0 in, the other 15 out *)
let SING0_EXPL =
  let hyps = [`&1 < l`; `l <= &1001 / &1000`; `a * a + b * b = &1`; `owalls c1 c2 a b l`] @
             [mem_osq (hd MARKER_PTS)] @ map (fun p -> mk_neg(mem_osq p)) (tl MARKER_PTS) in
  let concl = list_mk_conj (map mem_osq
     [`vector[&28 / &25; &1]:real^2`; `vector[&87 / &50; &1]:real^2`;
      `vector[&187 / &100; &19 / &25]:real^2`]) in
  prove(list_mk_forall(SPEC5, mk_imp(list_mk_conj hyps, concl)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN MARKERS_OUT ASSUME_TAC THENL
     [REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      ASM_REWRITE_TAC[MARKER_EXPLICIT] THEN FIRST_X_ASSUM CONTR_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])
                [SINGLETON_112; SINGLETON_174; SINGLETON_187]));;

let GEN5 th = GENL SPEC5 th;;
let T_RX th = GEN5 (RX_RULE th) and T_RY th = GEN5 (RY_RULE th)
and T_SW th = GEN5 (CONV_RULE REAL_RAT_REDUCE_CONV (SW_RULE (SPECL [`c2:real`; `c1:real`; `b:real`; `a:real`; `l:real`] th)));;

(* marker 0 is sent to marker k by these compositions *)
let SING_EXPL = Array.make 8 TRUTH;;
SING_EXPL.(0) <- SING0_EXPL;;
SING_EXPL.(1) <- T_SW SING0_EXPL;;
SING_EXPL.(2) <- T_RX SING0_EXPL;;
SING_EXPL.(3) <- T_RX (T_SW SING0_EXPL);;
SING_EXPL.(6) <- T_RY SING0_EXPL;;
SING_EXPL.(7) <- T_RY (T_SW SING0_EXPL);;
SING_EXPL.(4) <- T_RX (T_RY SING0_EXPL);;
SING_EXPL.(5) <- T_RX (T_RY (T_SW SING0_EXPL));;

(* ------------------------------------------------------------------------- *)
(* From  owned c1 c2 a b l = set_of_list c  to explicit marker facts.        *)
(* ------------------------------------------------------------------------- *)

let OWNED_MEMBER = prove
 (`forall c1 c2 a b l c j. owned c1 c2 a b l = set_of_list c /\ j < 16
     ==> (marker j IN osq c1 c2 a b l <=> MEM j c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; owned; IN_ELIM_THM; IN_SET_OF_LIST] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;

(* given th: |- owned c1 c2 a b l = set_of_list c (c a numeral list), the 16 facts *)
let marker_facts th =
  map (fun j ->
    let th1 = MATCH_MP OWNED_MEMBER (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
                 (mk_binop `(<):num->num->bool` (mk_small_numeral j) `16`)))) in
    let th2 = CONV_RULE (RAND_CONV (REWRITE_CONV[MEM] THENC NUM_REDUCE_CONV THENC
                                    REWRITE_CONV[])) th1 in
    REWRITE_RULE[MARKER_EXPLICIT] th2) (0--15);;

(* seed membership theorems for a square owning exactly set_of_list c *)
let seed_thms sqhyps th clist =
  let facts = marker_facts th in
  let base = filter (fun f -> not (is_neg (concl f))) facts in
  let extra =
    match clist with
      [k] when k < 8 ->
        let hs = conjuncts(lhand(snd(strip_forall(concl SING_EXPL.(k))))) in
        let prove_h h =
          try find (fun f -> aconv (concl f) h) (facts @ sqhyps)
          with Failure _ ->
            let rels = filter (fun f -> is_real_rel (concl f)) sqhyps in
            MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), h))) (end_itlist CONJ rels) in
        CONJUNCTS (MP (SPECL SPEC5 SING_EXPL.(k)) (end_itlist CONJ (map prove_h hs)))
    | _ -> [] in
  base @ extra;;

let pt_term (x,y) = mk_comb(`vector:(real)list->real^2`,
  mk_list([term_of_rat x; term_of_rat y],`:real`));;

let find_seed ths p =
  let pt = pt_term p in
  try find (fun th -> aconv (lhand(concl th)) pt) ths
  with Failure _ -> failwith ("find_seed: " ^ string_of_term pt);;

(* |- target IN osq ... from a triangle certificate *)
let tri_point ths (ps, target, s, t) =
  let [p0;p1;p2] = ps in
  let seg th0 th1 u =
    let (x0,y0) = (match dest_list(rand(lhand(concl th0))) with [x;y] -> x,y | _ -> failwith "")
    and (x1,y1) = (match dest_list(rand(lhand(concl th1))) with [x;y] -> x,y | _ -> failwith "") in
    let ut = term_of_rat u in
    let le0 = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_binop `(<=):real->real->bool` `&0` ut))
    and le1 = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_binop `(<=):real->real->bool` ut `&1`)) in
    let th = MATCH_MP OSQ_SEG (end_itlist CONJ [th0; th1; le0; le1]) in
    CONV_RULE (LAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)) th in
  let q01 = seg (find_seed ths p0) (find_seed ths p1) s in
  let th = seg q01 (find_seed ths p2) t in
  if aconv (lhand(concl th)) (pt_term target) then th
  else failwith "tri_point: target mismatch";;

let bits m = filter (fun k -> (m lsr k) land 1 = 1) (0--15);;
let numlist l = mk_list(map mk_small_numeral l, `:num`);;

let SQ2_HYPS = [`&1 < l`; `l <= &1001 / &1000`;
  `a * a + b * b = &1`; `owalls c1 c2 a b l`;
  `a' * a' + b' * b' = &1`; `owalls c1' c2' a' b' l`];;

let conflict_theorem (m, n, lseeds, rseeds, tl, tr) =
  let cl = bits m and dl = bits n in
  let ownp = mk_eq(`owned c1 c2 a b l`, mk_comb(`set_of_list:(num)list->num->bool`, numlist cl))
  and ownq = mk_eq(`owned c1' c2' a' b' l`, mk_comb(`set_of_list:(num)list->num->bool`, numlist dl)) in
  let hyps = map ASSUME SQ2_HYPS in
  let sqp = [el 0 hyps; el 1 hyps; el 2 hyps; el 3 hyps] in
  let sqq = [el 0 hyps; el 1 hyps; el 4 hyps; el 5 hyps] in
  let pth = ASSUME ownp and qth = ASSUME ownq in
  let pseeds = seed_thms sqp pth cl in
  (* the second square: reuse the machinery by renaming *)
  let ren = [`c1':real`,`c1:real`; `c2':real`,`c2:real`; `a':real`,`a:real`; `b':real`,`b:real`] in
  let qseeds0 = seed_thms (map (INST (map (fun (x,y) -> (y,x)) ren)) sqq)
                  (INST (map (fun (x,y) -> (y,x)) ren) qth) dl in
  let qseeds = map (INST ren) qseeds0 in
  let zp = tri_point pseeds tl and zq = tri_point qseeds tr in
  if not (aconv (lhand(concl zp)) (lhand(concl zq))) then failwith "conflict: targets differ" else
  let ex = EXISTS (mk_exists(`z:real^2`, mk_conj(mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, `z:real^2`), `osq c1 c2 a b l`),
                                                mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, `z:real^2`), `osq c1' c2' a' b' l`))),
                   lhand(concl zp)) (CONJ zp zq) in
  let th = itlist DISCH (SQ2_HYPS @ [ownp; ownq]) ex in
  GENL [`c1:real`; `c2:real`; `a:real`; `b:real`; `c1':real`; `c2':real`; `a':real`; `b':real`; `l:real`] th;;

let CONFLICT_THMS = map conflict_theorem HULL_CERTS;;

let CONF_LEMMA = prove
 (`forall c1 c2 a b l c d.
     NPACK c1 c2 a b l /\ ~(set_of_list c = set_of_list d) /\
     (forall p1 p2 pa pb q1 q2 qa qb.
        &1 < l ==> l <= &1001 / &1000 ==> pa * pa + pb * pb = &1 ==> owalls p1 p2 pa pb l ==>
        qa * qa + qb * qb = &1 ==> owalls q1 q2 qa qb l ==>
        owned p1 p2 pa pb l = set_of_list c ==> owned q1 q2 qa qb l = set_of_list d ==>
        exists z. z IN osq p1 p2 pa pb l /\ z IN osq q1 q2 qa qb l)
     ==> ~(set_of_list c IN FFP c1 c2 a b l /\ set_of_list d IN FFP c1 c2 a b l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`;
     `(b:num->real) i`; `(c1:num->real) j`; `(c2:num->real) j`; `(a:num->real) j`;
     `(b:num->real) j`]) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
         NPACK_SQ) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `j:num`]
         NPACK_SQ) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i:num = j` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC NPACK_DISJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                          `l:real`; `z:real^2`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let set_neq cl dl =
  let x = try find (fun x -> not (mem x dl)) cl with Failure _ -> find (fun x -> not (mem x cl)) dl in
  let tm = mk_neg(mk_eq(mk_comb(`set_of_list:(num)list->num->bool`, numlist cl),
                        mk_comb(`set_of_list:(num)list->num->bool`, numlist dl))) in
  prove(tm, REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC (mk_small_numeral x)) THEN
            REWRITE_TAC[IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

let NOCONF_OF_NPACK = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> NOCONF_FFP c1 c2 a b l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NOCONF_FFP; CONFL; ALL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) ->
    let s1 = lhand(lhand(rand w)) and s2 = lhand(rand(rand w)) in
    let cl = map dest_small_numeral (dest_list(rand s1)) and dl = map dest_small_numeral (dest_list(rand s2)) in
    let k = index (List.fold_left (fun a k -> a + (1 lsl k)) 0 cl, List.fold_left (fun a k -> a + (1 lsl k)) 0 dl)
                  (map (fun (m,n,_,_,_,_) -> (m,n)) HULL_CERTS) in
    MATCH_MP_TAC CONF_LEMMA THEN ASM_REWRITE_TAC[set_neq cl dl] THEN
    REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`p1:real`; `p2:real`; `pa:real`; `pb:real`; `q1:real`; `q2:real`; `qa:real`; `qb:real`; `l:real`]
                 (el k CONFLICT_THMS)) THEN
    REWRITE_TAC[]));;

let PACKING_REDUCED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> GOALF (FFP c1 c2 a b l)`,
  MESON_TAC[PACKING_CLASSIFIED; NOCONF_OF_NPACK]);;
