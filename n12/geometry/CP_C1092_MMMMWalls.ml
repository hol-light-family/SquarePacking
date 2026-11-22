(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMWalls.lean (N12Compact.C1092MMMMWalls).*)
(* Four actual MMMM wall origins.  Conventions of CP_C1092_MMMMStrictCore.ml *)
(* / CP_C1092_MMMMEntrance.ml: owners p i = OriginalOwners tuple at mask     *)
(* EL i c1092wc_code (side l), WallContext p mmmm = c1092wc_ctx .. mmmm.     *)
(* pullX / pullY: LINSIDE_PULLX / LINSIDE_PULLY (the pulled tuples are       *)
(* written out); WallProfile.boundary_origin: OCWPBO_BOUNDARY_ORIGIN;        *)
(* C1092OrdinaryHalfpoint.point: C1092OH_POINT; the transports by           *)
(* g = (T,F,F) follow C1092MMEN_NORTHWEST_PAIR (context_transport,           *)
(* family_transport, owners_transport).  Tag C1092MMW_.                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMMStrictCore.ml";;
needs "n12/geometry/CP_C1092_OrdinaryHalfpoint.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

let C1092MMW_V = C1092MMEN_V;;
let c1092mmw_q i = c1092mmsc_q i;;
let c1092mmw_pullx q = match q with
    [c; s; u; v; a] -> [mk_comb(`(--):real->real`, c); s;
      mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` c);
      mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a)
        (mk_binop `( * ):real->real->real` `&4` s); a]
  | _ -> failwith "c1092mmw_pullx";;
let c1092mmw_pully q = match q with
    [c; s; u; v; a] -> [c; mk_comb(`(--):real->real`, s);
      mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` s);
      mk_binop `(-):real->real->real` (mk_binop `(-):real->real->real`
        (mk_binop `( * ):real->real->real` `&4` c) v) a; a]
  | _ -> failwith "c1092mmw_pully";;

let c1092mmw_dis i j =
  let th = SPECL (C1092MMW_V @ [mk_small_numeral i; mk_small_numeral j]) C1092WC_OWNERS_DISJOINT in
  let rest = rand (rand (lhand (concl th))) in
  REWRITE_RULE[ldisj] (MP th (CONJ (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP)))
    (CONJ (CONJUNCT2 (ASSUME (parse_term C1092AE_HYP)))
      (EQT_ELIM ((NUM_REDUCE_CONV THENC REWRITE_CONV[]) rest)))));;

let c1092mmw_corner k =
  let th = MP (SPECL (C1092MMW_V @ [mk_small_numeral k]) C1092WC_CORNER_POINTS)
    (CONJ (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP)))
      (CONJ (CONJUNCT2 (ASSUME (parse_term C1092AE_HYP)))
        (EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral k) `4`))))) in
  CONV_RULE (REWRITE_CONV[c1092wc_corner; c1092wc_cpoint] THENC ONCE_DEPTH_CONV EL_CONV THENC
             REWRITE_CONV[]) th;;

let c1092mmw_box i =
  let m = mk_comb(mk_comb(`EL:num->(num)list->num`, mk_small_numeral i), `c1092wc_code`) in
  REWRITE_RULE[lcont] (MP (SPECL (C1092MMW_V @ [m]) OO_BOX) (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP))));;
let c1092mmw_unit i =
  let m = mk_comb(mk_comb(`EL:num->(num)list->num`, mk_small_numeral i), `c1092wc_code`) in
  MP (SPECL (C1092MMW_V @ [m]) OO_UNIT) (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP)));;
let C1092MMW_SIDE = MP (SPECL C1092MMW_V OO_SIDE) (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP)));;
let C1092MMW_POS = MP (REAL_ARITH `&1 < l ==> &0 < l`) C1092MMW_SIDE;;
let c1092mmw_inst th = UNDISCH (SPEC_ALL th);;
let c1092mmw_ctx th = MP (SPEC_ALL th) (CONJ (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP)))
  (CONJ (CONJUNCT2 (ASSUME (parse_term C1092AE_HYP))) (ASSUME (parse_term C1092MMEN_CTX))));;

(* close the antecedent of boundary_origin (after unfolding the pulls) *)
let C1092MMW_CLOSE_TAC facts =
  MAP_EVERY ASSUME_TAC facts THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE
   (REWRITE_TAC[REAL_NEG_MUL2] THEN FIRST_ASSUM ACCEPT_TAC) ORELSE
   (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) ORELSE
   (REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE
   (REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(fun b ->
      MP_TAC (MATCH_MP b th))) THEN REAL_ARITH_TAC));;

let c1092mmw_stmt concl = c1092mmsc_stmt concl;;

(* Lean: side_gt / side_same (private) are OO_SIDE / the common side l *)

let C1092MMW_MARKER11 = C1092MMSC_MARKER11;;
let C1092MMW_MARKER2 = c1092mmsc_marker true 2 48 4 "&3" "&1543 / &500";;
let C1092MMW_MARKER5 = c1092mmsc_marker true 5 512 9 "&47 / &20" "&33 / &20";;
let C1092MMW_MARKER9 = c1092mmsc_marker true 9 8192 13 "&2" "&457 / &500";;
let C1092MMW_MARKER1 = c1092mmsc_marker true 1 12 2 "&3" "&457 / &500";;

(* Lean: top_origin *)
let C1092MMW_TOP_ORIGIN = prove
 (c1092mmw_stmt (c1092mmsc_in 11 "&2" "&3"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let hyp = CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`) in
  let fix th = PROVE_HYP hyp (PROVE_HYP (ASSUME (parse_term C1092MMEN_CTX)) th) in
  let half = fix (c1092mmw_ctx C1092MMSC_RIGHT_HALFPOINT) in
  let d210 = fix (c1092mmw_dis 2 10) in
  let missingK = MP (TAUT `forall p q. ~(p /\ q) ==> q ==> ~p`
                       |> SPECL [parse_term (c1092mmsc_in 2 "&3" "&5 / &2"); concl half]) (SPECL [`&3`; `&5 / &2`] d210) in
  let missingK = MP missingK half in
  let facts = map fix
    [c1092mmw_unit 11; c1092mmw_unit 2; C1092MMW_SIDE; C1092MMW_POS;
     c1092mmw_box 11; c1092mmw_box 2;
     c1092mmw_inst C1092MMW_MARKER11; c1092mmw_ctx C1092MMEN_TOP_F;
     c1092mmw_inst C1092MMW_MARKER2; c1092mmw_corner 2; missingK; c1092mmw_dis 2 11] in
  MP_TAC(SPECL (c1092mmw_pully (c1092mmw_pullx (c1092mmw_q 11)) @
                c1092mmw_pully (c1092mmw_pullx (c1092mmw_q 2)) @ [`&457 / &500`; `&8 / &5`])
    OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[ldisj; LINSIDE_PULLY; LINSIDE_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [C1092MMW_CLOSE_TAC facts; SIMP_TAC[]]);;

(* the g = (T,F,F) transport of an MMMM owner point (as C1092MMEN_NORTHWEST_PAIR) *)
let c1092mmw_transport concl src i =
  let g = `(true,false,false)` and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  prove
   (c1092mmw_stmt concl,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `exists d1 d2 e1 e2. c1092ot_pk (true,false,false) (c1,c2,a,b) = (d1,d2,e1,e2)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
     [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
     [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `c1092wc_ctx d1 d2 e1 e2 l c1092mmen_mmmm` ASSUME_TAC THENL
     [MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
      EXISTS_TAC `c1092ws_branch_action (true,false,false) c1092mmen_mmmm` THEN
      REWRITE_TAC[C1092MMEN_ACTION] THEN
      MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`] src) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL ([g] @ v4 @ [`l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`;
                   mk_small_numeral i]) C1092OT_OWNERS_TRANSPORT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
    REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i))] THEN
    REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* Lean: right_origin *)
let C1092MMW_RIGHT_ORIGIN = c1092mmw_transport (c1092mmsc_in 10 "&3" "&2") C1092MMW_TOP_ORIGIN 11;;

let c1092mmw_excl th dis x y =
  let p = lhand (rand (concl (SPECL [x; y] dis))) in
  MP (MP (TAUT `forall p q. ~(p /\ q) ==> q ==> ~p` |> SPECL [p; concl th]) (SPECL [x; y] dis)) th;;

(* Lean: southeast_halfpoint *)
let C1092MMW_SOUTHEAST_HALFPOINT = prove
 (c1092mmw_stmt (c1092mmsc_in 5 "&3" "&3 / &2"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let hyp = CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`) in
  let fix th = PROVE_HYP hyp (PROVE_HYP (ASSUME (parse_term C1092MMEN_CTX)) th) in
  let ordinary = fix (c1092mmw_ctx C1092MMEN_SOUTHEAST_PAIR) in
  let inward = CONJUNCT2 (fix (REWRITE_RULE[c1092mmen_mmmm] (MP (SPEC_ALL C1092MMSC_INWARD)
    (CONJ (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP))) (CONJ (CONJUNCT2 (ASSUME (parse_term C1092AE_HYP))) (CONJ (ASSUME (parse_term C1092MMEN_CTX))
      (CONJ (REWRITE_CONV[c1092mmen_mmmm] `~c1092mmen_mmmm 2` |> EQT_ELIM)
            (REWRITE_CONV[c1092mmen_mmmm] `~c1092mmen_mmmm 3` |> EQT_ELIM)))))))) in
  let right = fix (c1092mmw_ctx C1092MMW_RIGHT_ORIGIN) in
  let corner = fix (c1092mmw_corner 1) in
  let wall = CONJUNCT2 (fix (MP (SPEC_ALL C1092MMEN_SOUTHWEST_HIGH_WALL_POINTS)
    (CONJ (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP))) (ASSUME (parse_term C1092MMEN_CTX))))) in
  let dis j = fix (c1092mmw_dis 5 j) in
  let ex th j = let x, y = (match snd (strip_comb (concl th)) with
        [_; _; _; _; _; x; y] -> x, y | _ -> failwith "ex") in c1092mmw_excl th (dis j) x y in
  let facts = [fix (c1092mmw_unit 5); fix C1092MMW_SIDE; fix C1092MMW_POS;
               fix (c1092mmw_inst C1092MMW_MARKER5); CONJUNCT1 ordinary; CONJUNCT2 ordinary;
               ex inward 6; ex right 10; ex corner 1; ex wall 9] in
  MATCH_MP_TAC C1092OH_POINT THEN REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC facts));;

(* Lean: northwest_halfpoint *)
let C1092MMW_NORTHWEST_HALFPOINT = c1092mmw_transport (c1092mmsc_in 7 "&3 / &2" "&3") C1092MMW_SOUTHEAST_HALFPOINT 5;;

(* Lean: bottom_origin *)
let C1092MMW_BOTTOM_ORIGIN = prove
 (c1092mmw_stmt (c1092mmsc_in 9 "&2" "&1"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let hyp = CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`) in
  let fix th = PROVE_HYP hyp (PROVE_HYP (ASSUME (parse_term C1092MMEN_CTX)) th) in
  let half = fix (c1092mmw_ctx C1092MMW_SOUTHEAST_HALFPOINT) in
  let missingK = c1092mmw_excl half (fix (c1092mmw_dis 1 5)) `&3` `&3 / &2` in
  let wall = CONJUNCT2 (fix (MP (SPEC_ALL C1092MMEN_SOUTHWEST_HIGH_WALL_POINTS)
    (CONJ (CONJUNCT1 (ASSUME (parse_term C1092AE_HYP))) (ASSUME (parse_term C1092MMEN_CTX))))) in
  let facts = map fix
    [c1092mmw_unit 9; c1092mmw_unit 1; C1092MMW_SIDE; C1092MMW_POS;
     c1092mmw_box 9; c1092mmw_box 1;
     c1092mmw_inst C1092MMW_MARKER9; c1092mmw_inst C1092MMW_MARKER1; c1092mmw_corner 1;
     c1092mmw_dis 1 9] @ [wall; missingK] in
  MP_TAC(SPECL (c1092mmw_pullx (c1092mmw_q 9) @ c1092mmw_pullx (c1092mmw_q 1) @
                [`&457 / &500`; `&87 / &50`]) OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[ldisj; LINSIDE_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [C1092MMW_CLOSE_TAC facts; SIMP_TAC[]]);;

(* Lean: left_origin *)
let C1092MMW_LEFT_ORIGIN = c1092mmw_transport (c1092mmsc_in 8 "&1" "&2") C1092MMW_BOTTOM_ORIGIN 9;;
