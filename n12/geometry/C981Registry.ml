(* ========================================================================= *)
(* Phase 2: Compact/Cases/C981Registry.lean (namespace                       *)
(* N12Compact.C981Compact).  The whole-vector registry of case 981: every    *)
(* one of the 117 original representatives has a full-vector exclusion.     *)
(* i : Fin 117 is i < 117; ExcludesVector (representativeVectors[i]!) is     *)
(* c981vd_excludes_vector (EL i c981vd_representative_vectors);              *)
(* List.range 117 is list_of_seq (\i. i) 117; List.filter (decide P) is      *)
(* FILTER P.  The Lean Prop Pending is the predicate c981reg_pending.        *)
(* Tag C981REG_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/C981RotatedEndpointRows.ml";;
needs "n12/geometry/C981DiagonalOuter.ml";;
needs "n12/geometry/C981WallElbows.ml";;
needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/C981FullAuxNegative.ml";;
needs "n12/geometry/C981DiagonalCornerElbows.ml";;
needs "n12/geometry/C981DiagonalOuterElbows.ml";;
needs "n12/geometry/C981TwoTipRows.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/C981InwardWallRows.ml";;
needs "n12/geometry/CP_C981_OutwardRows.ml";;
needs "n12/geometry/CP_C981_ShortRows_CoreRows.ml";;
needs "n12/geometry/CP_C981_ShortWallRows.ml";;
needs "n12/geometry/CP_C981_ShortWall71.ml";;
needs "n12/geometry/C981V116.ml";;
needs "n12/geometry/C981Progress.ml";;

(* Lean: baseCoveredIds *)
let c981reg_base_covered_ids = new_definition
 `c981reg_base_covered_ids =
    APPEND (APPEND (APPEND (APPEND c981rer_covered_ids c981do_covered_ids)
                           (APPEND c981we_covered_ids c981dwe_covered_ids))
                   c981ttr_covered_ids) c981iwr_covered_ids`;;

(* Lean: previousCoveredIds *)
let c981reg_previous_covered_ids = new_definition
 `c981reg_previous_covered_ids =
    APPEND (APPEND c981reg_base_covered_ids c981or_coveredIds) c981swr_covered_ids`;;

(* Lean: coveredIds *)
let c981reg_covered_ids = new_definition
 `c981reg_covered_ids = APPEND c981reg_previous_covered_ids c981p_completion_ids`;;

(* Lean: unfinished *)
let c981reg_unfinished = new_definition
 `c981reg_unfinished =
    FILTER (\i. ~MEM i c981reg_covered_ids /\ ~(i = 27) /\ ~(i = 116) /\ ~(i = 4) /\ ~(i = 6) /\
                ~(i = 5) /\ ~(i = 42) /\ ~(i = 3) /\ ~(i = 35) /\ ~(i = 60) /\ ~(i = 101) /\
                ~(i = 71))
           (list_of_seq (\i:num. i) 117)`;;

(* Lean: Pending *)
let c981reg_pending = new_definition
 `c981reg_pending <=>
    forall i. i < 117 /\ MEM i c981reg_unfinished
        ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`;;

(* ------------------------------------------------------------------------- *)
(* Literal forms and a FILTER evaluator.                                     *)
(* ------------------------------------------------------------------------- *)

let C981REG_MEM_RANGE = prove
 (`forall n i. MEM i (list_of_seq (\i:num. i) n) <=> i < n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[list_of_seq; MEM; MEM_APPEND; LT] THEN MESON_TAC[]);;

let C981REG_RANGE117 =
  let mk k = mk_comb(`list_of_seq (\i:num. i)`, k) in
  let rec go k th =
    if k = 117 then th else
    let th1 = REWRITE_CONV[list_of_seq] (mk (mk_comb(`SUC`, mk_small_numeral k))) in
    let th2 = CONV_RULE (LAND_CONV (RAND_CONV NUM_SUC_CONV)) (REWRITE_RULE[th; APPEND] th1) in
    go (k + 1) th2 in
  go 0 (REWRITE_CONV[list_of_seq] (mk `0`));;

let C981REG_LITS =
  [C981RER_COVERED_LIT; c981do_covered_ids; c981we_covered_ids; c981dwe_covered_ids;
   c981ttr_covered_ids; c981ttr_north_east_ids; c981ttr_north_west_ids; c981ttr_south_east_ids;
   c981iwr_covered_ids; c981or_coveredIds; c981swr_covered_ids; C981P_COMPLETIONIDS_EXACT];;

let C981REG_COVERED_LIT =
  REWRITE_RULE (C981REG_LITS @ [c981reg_previous_covered_ids; c981reg_base_covered_ids; APPEND])
    c981reg_covered_ids;;

(* evaluates FILTER P L for a literal L, P a lambda decided by the literal lists lits *)
let C981REG_FILTER_CONV lits =
  let dec = BETA_CONV THENC REWRITE_CONV(lits @ [MEM]) THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] in
  let ct, cf = CONJUNCT1 (SPEC_ALL COND_CLAUSES), CONJUNCT2 (SPEC_ALL COND_CLAUSES) in
  let rec filt tm =
    (REWR_CONV (CONJUNCT1 FILTER) ORELSEC
     (REWR_CONV (CONJUNCT2 FILTER) THENC RATOR_CONV (RATOR_CONV (RAND_CONV dec)) THENC
      ((REWR_CONV ct THENC RAND_CONV filt) ORELSEC (REWR_CONV cf THENC filt)))) tm in
  REWRITE_CONV lits THENC filt;;

(* Lean: wall_new_ids *)
let C981REG_WALL_NEW_IDS = prove
 (`FILTER (\i. ~MEM i c981rer_covered_ids /\ ~MEM i c981do_covered_ids /\ ~(i = 116))
          c981we_covered_ids =
   [0;8;19;22;44;50;52;53;66;111;113;114;115]`,
  CONV_TAC(LAND_CONV(C981REG_FILTER_CONV (C981REG_LITS @ [APPEND]))) THEN REFL_TAC);;

(* Lean: double_wall_new_ids *)
let C981REG_DOUBLE_WALL_NEW_IDS = prove
 (`FILTER (\i. ~MEM i c981rer_covered_ids /\ ~MEM i c981do_covered_ids /\
               ~MEM i c981we_covered_ids /\ ~(i = 116))
          c981dwe_covered_ids =
   [1;20;21;23;51;112]`,
  CONV_TAC(LAND_CONV(C981REG_FILTER_CONV (C981REG_LITS @ [APPEND]))) THEN REFL_TAC);;

(* Lean: two_tip_new_ids *)
let C981REG_TWO_TIP_NEW_IDS = prove
 (`FILTER (\i. ~MEM i c981rer_covered_ids /\ ~MEM i c981do_covered_ids /\
               ~MEM i c981we_covered_ids /\ ~MEM i c981dwe_covered_ids /\ ~(i = 116) /\
               ~(i = 4) /\ ~(i = 6) /\ ~(i = 5) /\ ~(i = 42) /\ ~(i = 3) /\ ~(i = 35) /\
               ~(i = 60))
          c981ttr_covered_ids =
   [25;31;40;70;32;33;38;57;99;94;95]`,
  CONV_TAC(LAND_CONV(C981REG_FILTER_CONV (C981REG_LITS @ [APPEND]))) THEN REFL_TAC);;

(* Lean: unfinished_ids *)
let C981REG_UNFINISHED_IDS = prove
 (`c981reg_unfinished = []`,
  REWRITE_TAC[c981reg_unfinished; C981REG_RANGE117] THEN
  CONV_TAC(LAND_CONV(C981REG_FILTER_CONV [C981REG_COVERED_LIT])) THEN REFL_TAC);;

(* Lean: unfinished_count *)
let C981REG_UNFINISHED_COUNT = prove
 (`LENGTH c981reg_unfinished = 0`,
  REWRITE_TAC[C981REG_UNFINISHED_IDS; LENGTH]);;

(* Lean: pending_closed *)
let C981REG_PENDING_CLOSED = prove
 (`c981reg_pending`,
  REWRITE_TAC[c981reg_pending; C981REG_UNFINISHED_IDS; MEM]);;

(* Lean: all_representatives *)
let C981REG_ALL_REPRESENTATIVES = prove
 (`c981reg_pending ==>
   forall i. i < 117 ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  let covered =
    [C981RER_COVERED_EXCLUDED; C981DO_COVERED_EXCLUDED; C981WE_COVERED_EXCLUDED;
     C981DWE_COVERED_EXCLUDED; C981TTR_COVERED_EXCLUDED; C981IWR_COVERED_EXCLUDED;
     C981OR_COVERED_EXCLUDED; C981SWR_COVERED_EXCLUDED; C981P_COMPLETION_EXCLUDED] in
  let singles =
    [`27`, C981BR27_REPRESENTATIVE27_EXCLUDED; `116`, C981V116_REPRESENTATIVE116_EXCLUDED;
     `4`, C981FAN_REPRESENTATIVE4_EXCLUDED; `6`, C981DCE_REPRESENTATIVE6_EXCLUDED;
     `5`, C981DCE_REPRESENTATIVE5_EXCLUDED; `42`, C981DCE_REPRESENTATIVE42_EXCLUDED;
     `3`, C981FAN_REPRESENTATIVE3_EXCLUDED; `35`, C981DOE_REPRESENTATIVE35_EXCLUDED;
     `60`, C981DOE_REPRESENTATIVE60_EXCLUDED; `101`, C981SRCR_REPRESENTATIVE101_EXCLUDED;
     `71`, C981SW71_REPRESENTATIVE71_EXCLUDED] in
  let case_tac (n, th) =
    ASM_CASES_TAC (mk_eq(`i:num`, n)) THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ACCEPT_TAC th; ALL_TAC] in
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `MEM (i:num) c981reg_covered_ids` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC[c981reg_covered_ids; c981reg_previous_covered_ids; c981reg_base_covered_ids;
                MEM_APPEND] THEN
    REPEAT STRIP_TAC THEN
    FIRST (map (fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC) covered);
    ALL_TAC] THEN
  EVERY (map case_tac singles) THEN
  UNDISCH_TAC `c981reg_pending` THEN REWRITE_TAC[c981reg_pending] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[c981reg_unfinished; MEM_FILTER; C981REG_MEM_RANGE]);;

(* Lean: all_representatives_complete *)
let C981REG_ALL_REPRESENTATIVES_COMPLETE =
  MP C981REG_ALL_REPRESENTATIVES C981REG_PENDING_CLOSED;;
