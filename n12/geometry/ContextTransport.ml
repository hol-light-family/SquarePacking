(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallSymmetry/ContextTransport.lean.          *)
(* The wall-center cuts and strict forced points move with the same actual  *)
(* owners.  Conventions of OwnerTransport.ml / C1092WallCycle.ml /           *)
(* Actions.ml: a Transform is (sw, rx, ry); g.pullPacking p is the packing  *)
(* (d1,d2,e1,e2) with c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) (side l);    *)
(* wallFrame p k is c1092wc_wf{c,s,u,v} c1 c2 a b l k (side l);              *)
(* WallContext is c1092wc_ctx.  S12.Transform.apply g x y is the pair        *)
(* (c1092ct_apx g x y, c1092ct_apy g x y); S12.inside_pull is               *)
(* C1092CT_INSIDE_PULL (stated for a 5-tuple equation q' = pull g q).        *)
(* Tag C1092CT_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/OwnerTransport.ml";;

(* Lean: S12.Transform.apply *)
let c1092ct_apx = define
 `c1092ct_apx (sw,rx,ry) (x:real) (y:real) =
    let u = if sw then y else x in if rx then &4 - u else u`;;
let c1092ct_apy = define
 `c1092ct_apy (sw,rx,ry) (x:real) (y:real) =
    let v = if sw then x else y in if ry then &4 - v else v`;;

(* Lean: S12.inside_pull *)
let C1092CT_INSIDE_PULL = prove
 (`forall g c s u v a c' s' u' v' a' x y.
     (c',s',u',v',a') = c1092ot_pull g (c,s,u,v,a)
     ==> (linside c' s' u' v' a' x y <=> linside c s u v a (c1092ct_apx g x y) (c1092ct_apy g x y))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ot_pull; c1092ot_px; c1092ot_py; c1092ot_psw; I_THM; PAIR_EQ;
              c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092CT_WA_LT = prove
 (`forall g k. k < 4 ==> c1092ws_wall_action g k < 4`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ws_wall_action; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC C1092WS_LOOKUPS THEN CONV_TAC NUM_REDUCE_CONV);;

(* the local-frame center under a pulled square *)
let C1092CT_LOCAL_CENTER = prove
 (`forall g k c s u v a c' s' u' v' a'.
     k < 4 /\ c * c + s * s = &1 /\ (c',s',u',v',a') = c1092ot_pull g (c,s,u,v,a)
     ==> lcy (c1092wc_lfc k c' s' u' v' a') (c1092wc_lfs k c' s' u' v' a')
             (c1092wc_lfu k c' s' u' v' a') (c1092wc_lfv k c' s' u' v' a') a' =
         if c1092ws_wall_flip g k
         then &4 - lcy (c1092wc_lfc (c1092ws_wall_action g k) c s u v a)
                       (c1092wc_lfs (c1092ws_wall_action g k) c s u v a)
                       (c1092wc_lfu (c1092ws_wall_action g k) c s u v a)
                       (c1092wc_lfv (c1092ws_wall_action g k) c s u v a) a
         else lcy (c1092wc_lfc (c1092ws_wall_action g k) c s u v a)
                  (c1092wc_lfs (c1092ws_wall_action g k) c s u v a)
                  (c1092wc_lfu (c1092ws_wall_action g k) c s u v a)
                  (c1092wc_lfv (c1092ws_wall_action g k) c s u v a) a`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ot_pull; c1092ot_px; c1092ot_py; c1092ot_psw; I_THM; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[c1092ws_wall_action; c1092ws_wall_flip; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC C1092WS_LOOKUPS THEN
  REWRITE_TAC[EL; HD; TL; num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  REWRITE_TAC[c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_CLAUSES; lcy] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING);;

(* Lean: wall_center_transport *)
let C1092CT_WALL_CENTER_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 k.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ k < 4
     ==> lcy (c1092wc_wfc d1 d2 e1 e2 l k) (c1092wc_wfs d1 d2 e1 e2 l k)
             (c1092wc_wfu d1 d2 e1 e2 l k) (c1092wc_wfv d1 d2 e1 e2 l k) l =
         if c1092ws_wall_flip g k
         then &4 - lcy (c1092wc_wfc c1 c2 a b l (c1092ws_wall_action g k))
                       (c1092wc_wfs c1 c2 a b l (c1092ws_wall_action g k))
                       (c1092wc_wfu c1 c2 a b l (c1092ws_wall_action g k))
                       (c1092wc_wfv c1 c2 a b l (c1092ws_wall_action g k)) l
         else lcy (c1092wc_wfc c1 c2 a b l (c1092ws_wall_action g k))
                  (c1092wc_wfs c1 c2 a b l (c1092ws_wall_action g k))
                  (c1092wc_wfu c1 c2 a b l (c1092ws_wall_action g k))
                  (c1092wc_wfv c1 c2 a b l (c1092ws_wall_action g k)) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv] THEN
  MATCH_MP_TAC C1092CT_LOCAL_CENTER THEN ASM_SIMP_TAC[OO_UNIT] THEN
  MATCH_MP_TAC C1092OT_WALL_TRANSPORT THEN ASM_REWRITE_TAC[]);;

(* Lean: wall_point_transport (private) *)
let C1092CT_WALL_POINT_TRANSPORT = prove
 (`forall g k bb x y. k < 4
     ==> c1092ct_apx g (c1092wc_pmx k x (c1092wc_by (if c1092ws_wall_flip g k then ~bb else bb) y))
                       (c1092wc_pmy k x (c1092wc_by (if c1092ws_wall_flip g k then ~bb else bb) y)) =
         c1092wc_pmx (c1092ws_wall_action g k) x (c1092wc_by bb y) /\
         c1092ct_apy g (c1092wc_pmx k x (c1092wc_by (if c1092ws_wall_flip g k then ~bb else bb) y))
                       (c1092wc_pmy k x (c1092wc_by (if c1092ws_wall_flip g k then ~bb else bb) y)) =
         c1092wc_pmy (c1092ws_wall_action g k) x (c1092wc_by bb y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`; `bb:bool`] THEN
  REWRITE_TAC[c1092ws_wall_action; c1092ws_wall_flip; c1092ct_apx; c1092ct_apy;
              LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC C1092WS_LOOKUPS THEN
  REWRITE_TAC[EL; HD; TL; num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_CLAUSES] THEN REAL_ARITH_TAC);;

(* Lean: forced_point_transport *)
let C1092CT_FORCED_POINT_TRANSPORT = prove
 (`forall g br k i. k < 4
     ==> c1092ct_apx g (c1092wc_fpx k (c1092ws_branch_action g br k) i)
                       (c1092wc_fpy k (c1092ws_branch_action g br k) i) =
         c1092wc_fpx (c1092ws_wall_action g k) (br (c1092ws_wall_action g k)) i /\
         c1092ct_apy g (c1092wc_fpx k (c1092ws_branch_action g br k) i)
                       (c1092wc_fpy k (c1092ws_branch_action g br k) i) =
         c1092wc_fpy (c1092ws_wall_action g k) (br (c1092ws_wall_action g k)) i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[c1092wc_fpx; c1092wc_fpy; c1092ws_branch_action] THEN
  ASM_SIMP_TAC[C1092CT_WALL_POINT_TRANSPORT]);;

(* Lean: context_transport *)
let C1092CT_CONTEXT_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 br.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ c1092wc_ctx c1 c2 a b l br
     ==> c1092wc_ctx d1 d2 e1 e2 l (c1092ws_branch_action g br)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c1092wc_ctx] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c1092ws_wall_action g k` o REWRITE_RULE[c1092wc_ctx]) THEN
  ASM_SIMP_TAC[C1092CT_WA_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`g:bool#bool#bool`; `c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                `l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `k:num`]
    C1092CT_WALL_CENTER_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(fun cut -> CONJ_TAC THENL
   [MP_TAC cut THEN REWRITE_TAC[c1092ws_branch_action] THEN
    ASM_CASES_TAC `c1092ws_wall_flip g k` THEN
    ASM_CASES_TAC `(br:num->bool) (c1092ws_wall_action g k)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g:bool#bool#bool`; `c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                  `l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `k:num`]
      C1092OT_WALL_TRANSPORT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
    ASM_SIMP_TAC[C1092CT_FORCED_POINT_TRANSPORT]]));;
