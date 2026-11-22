(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F5ThreeSquareEntrance.lean     *)
(* (N12Compact.Completion.OtherCases.C983).  Original actual owners supply   *)
(* the E/N/R entrance of the negative three-square ending.  Conventions of   *)
(* CP_OtherCases_C983_F5NegativeEntrance.ml: owners p 5 / 6 / 10 = owner     *)
(* 512 / 1024 / 16384; (owners p 10).translated 2 2 is the tuple of          *)
(* C983AOP_TRANSLATE.  RightTripleData.Input / right_frame = ocrtd_input /   *)
(* OCRTD_RIGHT_FRAME, f5_negative_entrance C983FNE_F5_NEGATIVE_ENTRANCE,     *)
(* f5_top_only_points C983F5TOP_F5_TOP_ONLY_POINTS, f5_right_final           *)
(* C983F5RF_F5_RIGHT_FINAL, right_advance_of_omitted_lower                   *)
(* c983f5top_advance, f5_southeast_g6 C983F5_F5_SOUTHEAST_G6.  The           *)
(* existential squares carry their OpenSquare invariants.  F5TripleInput is  *)
(* c983f5tse_tripleinput.  Tag C983F5TSE_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5NegativeEntrance.ml";;
needs "n12/geometry/CP_OtherCases_RightTripleData.ml";;

let C983F5TSE_R = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`];;

let c983f5tse_concl inp =
  let xv = `x:real` and yv = `y:real` in
  let plus2 t = mk_binop `(+):real->real->real` t `&2` in
  let inq q x y = list_mk_comb(`linside`, q @ [x; y]) in
  let iffq q m = list_mk_forall([xv; yv], mk_iff(inq q xv yv, c983ab_in m (plus2 xv) (plus2 yv))) in
  let sq = C983FNE_E @ C983FNE_N @ C983F5TSE_R in
  list_mk_exists(sq, list_mk_conj
    [`cE * cE + sE * sE = &1`; `&0 < aE`; `cr * cr + sr * sr = &1`; `&0 < ar`;
     `cR * cR + sR * sR = &1`; `&0 < aR`;
     list_mk_comb(inp, sq);
     iffq C983FNE_E 512; iffq C983FNE_N 1024; iffq C983F5TSE_R 16384]);;

(* translated 2 2 of a 5-tuple *)
let c983f5tse_tr t = match t with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&2`) (mul s `&2`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&2`) (mul c `&2`)); a]
  | _ -> failwith "c983f5tse_tr";;

(* the common proof; extra apartness facts for the unfolded input *)
let C983F5TSE_TAC inp_defs pairs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f5 = ASSUME (c983f4f_mem 5 7) in
  let points = c983f5_use C983F5TOP_F5_TOP_ONLY_POINTS [f5] in
  let final = c983f5top_use C983F5RF_F5_RIGHT_FINAL [f5] in
  let dec tm = EQT_ELIM ((REWRITE_CONV[final; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) tm) in
  let adv = c983f5top_advance (dec (c983f4f_mem 19 10)) (dec (mk_neg (c983f4f_mem 8 10))) in
  let origin = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 points)) in
  let tR = c983f5tse_tr (c983ab_own 16384) in
  let bx = REWRITE_RULE[lcont] (box 16384) in
  let elbow = c983f4f_point (c983f5_use C983F5_F5_SOUTHEAST_G6 [f5]) in
  let facts = [seed 5 `&47 / &20` `&33 / &20`; elbow; CONJUNCT1 points] in
  let aparts = map (fun (m, n) -> apart m n) pairs in
  MP_TAC(c983f5_use C983FNE_F5_NEGATIVE_ENTRANCE [f5]) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC (C983FNE_E @ C983FNE_N) THEN STRIP_TAC THEN
  MP_TAC(SPECL tR OCRTD_RIGHT_FRAME) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[C983AOP_TRANSLATE] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN
    FIRST [ACCEPT_TAC (unit 16384); ACCEPT_TAC pos; ACCEPT_TAC origin; ACCEPT_TAC adv;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP bx) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; C983AOP_TRANSLATE] THEN
  MAP_EVERY X_GEN_TAC C983F5TSE_R THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(v, `l:real`))))
    [`aE:real`; `ar:real`; `aR:real`] THEN
  MAP_EVERY EXISTS_TAC (map (subst [`l:real`,`aE:real`; `l:real`,`ar:real`; `l:real`,`aR:real`])
                         (C983FNE_E @ C983FNE_N @ C983F5TSE_R)) THEN
  REWRITE_TAC(inp_defs @ [ocrtd_input]) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
         ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
         FIRST (map ACCEPT_TAC facts @
                map (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC th) aparts)];;

(* Lean: f5_three_square_entrance *)
let C983F5TSE_F5_THREE_SQUARE_ENTRANCE = prove
 (c983sa_stmt [c983f4f_mem 5 7] (c983f5tse_concl `ocrtd_input`),
  C983F5TSE_TAC [] [512, 16384; 1024, 16384]);;

(* Lean: F5TripleInput *)
let c983f5tse_tripleinput = new_definition
 `c983f5tse_tripleinput (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                        (cN:real) (sN:real) (uN:real) (vN:real) (aN:real)
                        (cR:real) (sR:real) (uR:real) (vR:real) (aR:real) <=>
    ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
    (forall x y. ~(linside cE sE uE vE aE x y /\ linside cN sN uN vN aN x y))`;;

(* Lean: f5_pairwise_three_square_entrance *)
let C983F5TSE_F5_PAIRWISE_THREE_SQUARE_ENTRANCE = prove
 (c983sa_stmt [c983f4f_mem 5 7] (c983f5tse_concl `c983f5tse_tripleinput`),
  C983F5TSE_TAC [c983f5tse_tripleinput] [512, 16384; 1024, 16384; 512, 1024]);;
