(* ========================================================================= *)
(* Port, layer 8: geometry for the local rejections (Jatloe: ShortCluster,   *)
(* FourPointCertificate, WallBridge).                                        *)
(* ========================================================================= *)

needs "n12/phase1/singleton.ml";;

(* "inside points ==> one of the outside points", for short outside clusters *)
let short_lemma ins outs =
  let pt (x,y) = mk_comb(`vector:(real)list->real^2`, mk_list([x;y],`:real`)) in
  let mem p = mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, pt p), `osq c1 c2 a b l`) in
  let tm = list_mk_forall(SPEC5, mk_imp(list_mk_conj ([`&1 < l`; `a * a + b * b = &1`] @ map mem ins),
                                       list_mk_disj (map mem outs))) in
  let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in
  let cs ((x0,y0),(x1,y1)) =
    let dx = mk_binop `(-):real->real->real` x0 x1 and dy = mk_binop `(-):real->real->real` y0 y1 in
    MP_TAC(SPECL [`a:real`; `b:real`; dx; dy] CS_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= &1 <=> -- &1 <= x /\ x <= &1`] THEN STRIP_TAC in
  prove(tm,
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN STRIP_TAC THEN
    MAP_EVERY cs (pairs outs) THEN
    REFUTE_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM; REAL_NOT_LT]) THEN
    NLIN_TAC ~deg2:false []);;


let WB_UPPER = prove
 (`forall X Y c s l t.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= X /\
        vector[&457 / &500; &1] IN osq X Y c s l /\ vector[&457 / &500; &2] IN osq X Y c s l /\
        &5 / &4 <= t /\ t <= &7 / &4
        ==> (&1 - X) * c + (t - Y) * s < l / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN STRIP_TAC THEN
  FRAME_FACTS_TAC THEN REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  NLIN_FACTS_TAC [] [`s * (&2 - t) < (&43 / &500) * c`; `s <= (&43 / &125) * c`; `s <= c`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`] [`&2 / &3 <= c`] THEN
  NLIN_FACTS_TAC [] [`l * c <= c * c + (&457 / &500) * s * s - (&2 - t) * c * s`;
    `(&457 / &500 - &2 / &5) * s <= (&2 - t) * c`; `&0 <= (&1 - c) * (c - &2 / &3)`;
    `&0 < (l - &1) * c`; `c <= &1`] THEN
  NLIN_TAC []);;

let WALL_BRIDGE_FRAME = prove
 (`forall X Y c s l t.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= X /\
        vector[&457 / &500; &1] IN osq X Y c s l /\ vector[&457 / &500; &2] IN osq X Y c s l /\
        &5 / &4 <= t /\ t <= &7 / &4
        ==> vector[&1; t] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`X:real`; `Y:real`; `c:real`; `s:real`; `l:real`; `t:real`] WB_UPPER) THEN
  MP_TAC(SPECL [`X:real`; `&3 - Y`; `s:real`; `c:real`; `l:real`; `&3 - t`] WB_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `forall x y. vector[x; y] IN osq X (&3 - Y) s c l <=> vector[x; &3 - y] IN osq X Y c s l`
   (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_OSQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `vector[&457 / &500; &1] IN osq X Y c s l` THEN
  UNDISCH_TAC `vector[&457 / &500; &2] IN osq X Y c s l` THEN
  REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN REPEAT STRIP_TAC THEN FRAME_FACTS_TAC THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
  NLIN_TAC [SQ_NONNEG `c - s`]);;

let WALL_BRIDGE_FORCES = prove
 (`forall c1 c2 a b l t.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        vector[&457 / &500; &1] IN osq c1 c2 a b l /\ vector[&457 / &500; &2] IN osq c1 c2 a b l /\
        &5 / &4 <= t /\ t <= &7 / &4
        ==> vector[&1; t] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MATCH_MP_TAC WALL_BRIDGE_FRAME THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `osq c1 c2 a b l = osq c1 c2 c s l`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
