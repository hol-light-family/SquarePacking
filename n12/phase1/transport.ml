(* ========================================================================= *)
(* Port, layer 10: D4 transport of a normalized packing (Jatloe:             *)
(* FamilyTransport, Symmetry).  Moving every square by a symmetry of the     *)
(* container gives a normalized packing whose marker family is the image of  *)
(* the old one under the marker permutation dperm t.                         *)
(* ========================================================================= *)

needs "n12/phase1/bridge.ml";;

let MPERM_L t = el t (dest_list(rhs(concl MPERMS)));;

let mperm_fun t = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(num)list->num`, `k:num`), MPERM_L t));;

(* the three generators: (index in MPERMS, square map, point map) *)
let GEN_RY = 1 and GEN_RX = 2 and GEN_SW = 4;;

let OSQ_MAP_RY = prove
 (`forall z c1 c2 a b l. z IN osq c1 (&4 - c2) b a l <=> vector[z$1; &4 - z$2] IN osq c1 c2 a b l`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC);;
let OSQ_MAP_RX = prove
 (`forall z c1 c2 a b l. z IN osq (&4 - c1) c2 b a l <=> vector[&4 - z$1; z$2] IN osq c1 c2 a b l`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC);;
let OSQ_MAP_SW = prove
 (`forall z c1 c2 a b l. z IN osq c2 c1 b a l <=> vector[z$2; z$1] IN osq c1 c2 a b l`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC);;

(* marker (p k) = map (marker k), k < 16, for a generator *)
let marker_perm_thm t mapfn =
  let p = mperm_fun t in
  prove(mk_forall(`k:num`, mk_imp(`k < 16`,
         mk_eq(mk_comb(`marker`, mk_comb(p, `k:num`)), mapfn `marker k`))),
    REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; VEC2_EQ_LOCAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV);;

let MARKER_PERM_RY = marker_perm_thm GEN_RY (fun m -> mk_comb(`vector:(real)list->real^2`,
   mk_list([mk_comb(mk_comb(`($):real^2->num->real`, m), `1`);
            mk_binop `(-):real->real->real` `&4` (mk_comb(mk_comb(`($):real^2->num->real`, m), `2`))], `:real`)));;
let MARKER_PERM_RX = marker_perm_thm GEN_RX (fun m -> mk_comb(`vector:(real)list->real^2`,
   mk_list([mk_binop `(-):real->real->real` `&4` (mk_comb(mk_comb(`($):real^2->num->real`, m), `1`));
            mk_comb(mk_comb(`($):real^2->num->real`, m), `2`)], `:real`)));;
let MARKER_PERM_SW = marker_perm_thm GEN_SW (fun m -> mk_comb(`vector:(real)list->real^2`,
   mk_list([mk_comb(mk_comb(`($):real^2->num->real`, m), `2`);
            mk_comb(mk_comb(`($):real^2->num->real`, m), `1`)], `:real`)));;

(* each generator permutation is an involution on 0..15 *)
let perm_invol t =
  let p = mperm_fun t in
  prove(mk_forall(`k:num`, mk_imp(`k < 16`, mk_conj(mk_comb(mk_comb(`(<):num->num->bool`, mk_comb(p, `k:num`)), `16`),
          mk_eq(mk_comb(p, mk_comb(p, `k:num`)), `k:num`)))),
    REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV);;
let INVOL_RY = perm_invol GEN_RY and INVOL_RX = perm_invol GEN_RX and INVOL_SW = perm_invol GEN_SW;;

let OWNED_SUBSET = prove
 (`forall c1 c2 a b l k. k IN owned c1 c2 a b l ==> k < 16`,
  SIMP_TAC[owned; IN_ELIM_THM]);;

(* owned of the moved square is the permuted owned set *)
let owned_map_thm osqmap mperm invol (c1',c2',a',b') =
  let pf = rator(rand(lhand(rand(snd(dest_forall(concl mperm)))))) in
  prove(list_mk_forall(SPEC5, mk_eq(list_mk_comb(`owned`, [c1';c2';a';b';`l:real`]),
          mk_comb(mk_comb(`IMAGE:(num->num)->(num->bool)->num->bool`, pf), `owned c1 c2 a b l`))),
    REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[owned; IN_ELIM_THM] THEN
    CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[osqmap])) THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC (mk_comb(pf, `j:num`)) THEN
      MP_TAC(SPEC `j:num` invol) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `j:num` mperm) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[VECTOR_2];
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `k:num` invol) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC (mk_comb(pf, `k:num`)) mperm) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

let OWNED_RY = owned_map_thm OSQ_MAP_RY MARKER_PERM_RY INVOL_RY (`c1:real`, `&4 - c2`, `b:real`, `a:real`);;
let OWNED_RX = owned_map_thm OSQ_MAP_RX MARKER_PERM_RX INVOL_RX (`&4 - c1`, `c2:real`, `b:real`, `a:real`);;
let OWNED_SW = owned_map_thm OSQ_MAP_SW MARKER_PERM_SW INVOL_SW (`c2:real`, `c1:real`, `b:real`, `a:real`);;

let DISJ_MAP_TAC osqmap =
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [osqmap] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `z:real^2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(`vector:(real)list->real^2`, mk_list([`z$1`; `z$2`], `:real`))));;

let npack_map_thm osqmap owalls_map ownedmap (c1f, c2f, af, bf) =
  let pf = rand(rator(rhs(snd(strip_forall(concl ownedmap))))) in
  let tm = list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(`NPACK c1 c2 a b l`,
      mk_conj(list_mk_comb(`NPACK`, [c1f; c2f; af; bf; `l:real`]),
        mk_eq(list_mk_comb(`FFP`, [c1f; c2f; af; bf; `l:real`]),
              mk_comb(mk_comb(`IMAGE:((num->bool)->(num->bool))->((num->bool)->bool)->((num->bool)->bool)`,
                 mk_comb(`IMAGE:(num->num)->(num->bool)->(num->bool)`, pf)), `FFP c1 c2 a b l`))))) in
  prove(tm,
    REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `NPACK c1 c2 a b l` THEN REWRITE_TAC[NPACK] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[owalls_map] THEN CONJ_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_MESON_TAC[];
        REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_TAC THEN ONCE_REWRITE_TAC[osqmap] THEN GEN_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[FFP; GSYM IMAGE_o; o_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[ownedmap])) THEN REFL_TAC]);;

let NPACK_RY = npack_map_thm OSQ_MAP_RY OWALLS_RY OWNED_RY
  (`c1:num->real`, `\i. &4 - (c2:num->real) i`, `b:num->real`, `a:num->real`);;
let NPACK_RX = npack_map_thm OSQ_MAP_RX OWALLS_RX OWNED_RX
  (`\i. &4 - (c1:num->real) i`, `c2:num->real`, `b:num->real`, `a:num->real`);;
let NPACK_SW = npack_map_thm OSQ_MAP_SW OWALLS_SW OWNED_SW
  (`c2:num->real`, `c1:num->real`, `b:num->real`, `a:num->real`);;

(* compositions: generator sequences (first applied first) for t = 0..7 *)
let GEN_SEQ = [| []; [NPACK_RY]; [NPACK_RX]; [NPACK_RY; NPACK_RX]; [NPACK_SW];
                 [NPACK_SW; NPACK_RY]; [NPACK_SW; NPACK_RX]; [NPACK_SW; NPACK_RY; NPACK_RX] |];;

let IMAGE_EQ_ON = prove
 (`forall f g (s:A->bool). (forall x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;

let FFP_SUBSET16 = prove
 (`forall c1 c2 a b l G k. G IN FFP c1 c2 a b l /\ k IN G ==> k < 16`,
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[OWNED_SUBSET]);;

let transport_thm t =
  let npk = ASSUME `NPACK c1 c2 a b l` in
  let step (np, eq) g =
    let th = MATCH_MP g np in
    let np' = CONJUNCT1 th and eq' = CONJUNCT2 th in
    (np', TRANS eq' (AP_TERM (rator(rhs(concl eq'))) eq)) in
  let (np, eq) = itlist (fun g acc -> step acc g) (rev GEN_SEQ.(t))
                   (npk, REFL `FFP c1 c2 a b l`) in
  let args = snd(strip_comb(concl np)) in
  let (f1,f2,f3,f4) = (match args with [x1;x2;x3;x4;_] -> (x1,x2,x3,x4) | _ -> failwith "args") in
  let goal = mk_exists(`d1:num->real`, mk_exists(`d2:num->real`, mk_exists(`e1:num->real`, mk_exists(`e2:num->real`,
    mk_conj(`NPACK d1 d2 e1 e2 l`,
      mk_eq(`IMAGE binarysum (FFP d1 d2 e1 e2 l)`,
            mk_comb(mk_comb(`IMAGE:((num->bool)->num)->((num->bool)->bool)->num->bool`,
              mk_abs(`G:num->bool`, mk_comb(`binarysum`,
                mk_comb(mk_comb(`IMAGE:(num->num)->(num->bool)->num->bool`,
                  mk_comb(`dperm`, mk_small_numeral t)), `G:num->bool`)))), `FFP c1 c2 a b l`))))))) in
  let th = prove(mk_imp(`NPACK c1 c2 a b l`, goal),
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [f1; f2; f3; f4] THEN
    REWRITE_TAC[PROVE_HYP (ASSUME `NPACK c1 c2 a b l`) np] THEN
    REWRITE_TAC[PROVE_HYP (ASSUME `NPACK c1 c2 a b l`) eq; GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC IMAGE_EQ_ON THEN X_GEN_TAC `G:num->bool` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    (if t = 0 then GEN_REWRITE_TAC LAND_CONV [GSYM IMAGE_I] else ALL_TAC) THEN
    MATCH_MP_TAC IMAGE_EQ_ON THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k < 16` MP_TAC THENL [ASM_MESON_TAC[FFP_SUBSET16]; ALL_TAC] THEN
    SPEC_TAC(`k:num`,`k:num`) THEN REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[dperm; MPERMS] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[I_THM]) in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] th;;

let TRANSPORTS = Array.init 8 transport_thm;;

let PACKING_ROW = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> exists c1' c2' a' b' r. NPACK c1' c2' a' b' l /\ MEM r ROWS /\
                           IMAGE binarysum (FFP c1' c2' a' b' l) = set_of_list r`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PACKING_REDUCED) THEN REWRITE_TAC[GOALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` (X_CHOOSE_THEN `r:num list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `t < 8` THEN
  SUBGOAL_THEN `t < 8 ==> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7`
    (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THENL [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST (map (fun th -> MP_TAC(MATCH_MP th (ASSUME `NPACK c1 c2 a b l`)) THEN
                        STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`d1:num->real`; `d2:num->real`;
                          `e1:num->real`; `e2:num->real`; `r:num list`] THEN
                        ASM_REWRITE_TAC[] THEN NO_TAC) (Array.to_list TRANSPORTS)));;
