(* ========================================================================= *)
(* Port of Compact/Bridge/C696CentralReach.lean (namespace N12Compact.       *)
(* C696CentralReach).  Four strict central points of the actual original     *)
(* C696 packing.  Conventions of C696WallCycle.ml / SideSignPacking.ml:      *)
(* owners p i is the owner of mask EL i c696ssp_owner_masks; frame q i is    *)
(* q, pullSwap q, pullX (pullY q), pullX (pullY (pullSwap q)) (the 5-tuple   *)
(* c696cr_frame i idx of the owner with index idx, pull templates of         *)
(* p2_base LCONT_PULLX etc.).  ClosedInside = lclosed; ClosedPointExclusion  *)
(* .closed_segment / outside_of_closed = LCLOSED_SEGMENT / OUTSIDE_OF_CLOSED; *)
(* ClosedFrames.positive_frame = CLF_POSITIVE_FRAME; FourSquareANarrow.      *)
(* point_of_higher_R = FSAN_POINT_OF_HIGHER_R.  Tag C696CR_.                 *)
(* ========================================================================= *)

needs "n12/geometry/C696WallCycle.ml";;
needs "n12/geometry/FourSquareANarrow.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: centralOwner, foreignOwner *)
let C696CR_CENTRAL_OWNER = [7; 7; 6; 6] and C696CR_FOREIGN_OWNER = [4; 3; 1; 0];;
let C696CR_MASKS = [1; 2; 12; 16; 32; 192; 256; 1024; 4096; 8192; 16384; 32768];;

(* Lean: frame (as the lcont theorem of the frame of owner idx; the frame is its tuple) *)
let c696cr_box i idx =
  let b = MP (SPECL (C696SSP_VARS @ [mk_small_numeral (el idx C696CR_MASKS)]) OO_BOX) C696SSP_NP in
  match i with
    0 -> b
  | 1 -> MATCH_MP LCONT_PULLSW b
  | 2 -> MATCH_MP LCONT_PULLX (MATCH_MP LCONT_PULLY b)
  | _ -> MATCH_MP LCONT_PULLX (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLSW b));;
let c696cr_frame i idx = snd (strip_comb (concl (c696cr_box i idx)));;

(* Lean: frame_side (private; the side is l) and the unit normal of a frame *)
let c696cr_unit i idx =
  let f = c696cr_frame i idx in
  let ou = MP (SPECL (C696SSP_VARS @ [mk_small_numeral (el idx C696CR_MASKS)]) OO_UNIT) C696SSP_NP in
  let sq x = mk_binop `( * ):real->real->real` x x in
  let tm = mk_eq(mk_binop `(+):real->real->real` (sq (el 0 f)) (sq (el 1 f)), `&1`) in
  MP (REAL_RING (mk_imp(concl ou, tm))) ou;;

(* Lean: frame_inside (private) and central_inside / central_missing / foreign_inside
   (private): a query point of the owner idx, read in frame i *)
let c696cr_fact i idx (x, y) inside =
  let tm = list_mk_comb(`linside`, c696cr_frame i idx @ [x; y]) in
  let e = c696wc_frame_conv tm in
  let args = snd (strip_comb (rhs (concl e))) in
  let lab = C696SSP_LABEL idx in
  if inside then EQ_MP (SYM e) (c696ssp_inside lab (el 5 args, el 6 args))
  else EQ_MP (SYM (AP_TERM `(~)` e)) (c696ssp_outside lab (el 5 args, el 6 args));;

(* Lean: apart / frame_apart (private) *)
let c696cr_apart i idx idx' =
  let f = c696cr_frame i idx and f' = c696cr_frame i idx' in
  let tm = list_mk_forall([`x:real`; `y:real`], mk_neg(mk_conj(
    list_mk_comb(`linside`, f @ [`x:real`; `y:real`]), list_mk_comb(`linside`, f' @ [`x:real`; `y:real`])))) in
  let d = REWRITE_RULE[ldisj] (MP (SPEC_ALL (oo_apart `c696ssp_family` (el idx C696CR_MASKS) (el idx' C696CR_MASKS)))
                                  C696SSP_HH) in
  TAC_PROOF(([], tm), REPEAT GEN_TAC THEN CONV_TAC c696wc_frame_conv THEN MATCH_ACCEPT_TAC d);;

(* the frame-free part of frame_reach: positive frame + FourSquareANarrow.point_of_higher_R *)
let C696CR_REACH = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     lclosed c s u v a (&2) (&113 / &50) /\ lclosed c s u v a (&113 / &50) (&2) /\
     lclosed c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\ ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\ ~linside c s u v a (&3) (&5 / &2)
     ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aq:real = a`)) THEN
  SUBGOAL_THEN `linside cq sq uq vq a (&2) (&5 / &2)` MP_TAC THENL
   [MATCH_MP_TAC FSAN_POINT_OF_HIGHER_R THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Lean: close (private) is LINSIDE_CLOSED *)
let c696cr_rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm);;

(* Lean: frame_reach  (i = 0..3) *)
let c696cr_frame_reach i =
  let ca = el i C696CR_CENTRAL_OWNER and fo = el i C696CR_FOREIGN_OWNER in
  let fa = c696cr_frame i ca and fr = c696cr_frame i fo in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let cl th = MATCH_MP LINSIDE_CLOSED th in
  let a_ p = c696cr_fact i ca p true and m_ p = c696cr_fact i ca p false in
  let rlow = cl (c696cr_fact i fo (`&3`, `&12 / &5`) true)
  and rhigh = cl (c696cr_fact i fo (`&3`, `&72 / &25`) true) in
  let seg = MP (SPECL (fr @ [`&3`; `&12 / &5`; `&3`; `&72 / &25`; `&5 / &24`]) LCLOSED_SEGMENT)
               (end_itlist CONJ [rlow; rhigh; c696cr_rr `&0 <= &5 / &24`; c696cr_rr `&5 / &24 <= &1`]) in
  let rmid = CONV_RULE (RAND_CONV REAL_RAT_REDUCE_CONV THENC RATOR_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)) seg in
  let ap = c696cr_apart i ca fo in
  let posR = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  let outside cth =
    let args = snd (strip_comb (concl cth)) in
    MP (SPECL (fa @ fr @ [el 5 args; el 6 args]) OUTSIDE_OF_CLOSED)
       (end_itlist CONJ [c696cr_unit i fo; posR; ap; cth]) in
  MP (SPECL fa C696CR_REACH)
     (end_itlist CONJ [c696cr_unit i ca; side;
        cl (a_ (`&2`, `&113 / &50`)); cl (a_ (`&113 / &50`, `&2`)); cl (a_ (`&47 / &20`, `&47 / &20`));
        m_ (`&33 / &20`, `&33 / &20`); m_ (`&47 / &20`, `&33 / &20`); m_ (`&33 / &20`, `&47 / &20`);
        outside rlow; outside rmid]);;

let C696CR_FRAME_REACH =
  c696wc_close (c696wc_fix (end_itlist CONJ (map c696cr_frame_reach (0 -- 3))));;

(* Lean: central_points *)
let C696CR_CENTRAL_POINTS =
  let fr = CONJUNCTS (UNDISCH (SPEC_ALL C696CR_FRAME_REACH)) in
  c696wc_close (end_itlist CONJ (map (fun th -> EQ_MP (c696wc_frame_conv (concl th)) th) fr));;
