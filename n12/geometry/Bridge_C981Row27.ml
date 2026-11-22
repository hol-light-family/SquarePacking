(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981Row27.lean (namespace N12Compact.C981Row27).  *)
(* The complete original C981 representative 27.  All compulsory points come *)
(* from its original marker masks and exact auxiliary ownership vector.      *)
(*                                                                           *)
(* Also the small C981 vector toolkit c981br_* used by the other C981 bridge *)
(* files (C981DiagonalOuter, C981InwardWallRows, C981TwoTipRows, C981V116):  *)
(* for a literal vector V (a HOL list of 12 literal num sets),               *)
(*   c981br_entry V i   : |- !c1 c2 a b l. c981ow_vector c1 c2 a b l = V      *)
(*                             ==> ooaux c1 c2 a b l m_i = S_i               *)
(*   c981br_in V i P / c981br_out V i P : Lean `inside i P (by decide)` /    *)
(*        `outside i P (by decide)` (query_inside_sound/query_outside_sound) *)
(*        |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) =            *)
(*             ccc981ri_family /\ c981ow_vector c1 c2 a b l = V              *)
(*             ==> [~]linside (owners p i) P                                 *)
(*   c981br_apart V i j : owners_disjoint p hf i j (ldisj, same hypotheses). *)
(*   c981br_close G owners facts : proves c981vd_excludes_vector V by         *)
(*        applying the geometry theorem G to the owner 5-tuples (owner       *)
(*        indices `owners`); side/unit/containment premises from OO_SIDE,    *)
(*        OO_UNIT, OO_BOX, the other premises from the facts.                *)
(* owners p i = the OriginalOwners owner at mask EL i c981ow_masks.          *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/C981Row27.ml";;

let C981BR_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

let c981br_mask i = el i C981OW_MASKS;;

let c981br_owner i =
  let mt = mk_small_numeral (c981br_mask i) in
  map (fun f -> list_mk_comb(f, C981BR_VARS @ [mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

let c981br_entry vtm i =
  let th = SPECL (C981BR_VARS @ [vtm; mk_small_numeral i]) C981OW_OWNERSHIP_ENTRY_AT in
  let th1 = CONV_RULE (LAND_CONV (RAND_CONV NUM_REDUCE_CONV) THENC REWRITE_CONV[]) th in
  let th2 = CONV_RULE (RAND_CONV (LAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV c981ow_masks) THENC EL_CONV)) THENC
                                  RAND_CONV EL_CONV)) th1 in
  GENL C981BR_VARS th2;;

let C981BR_HYP vtm =
  list_mk_conj [`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family`;
                mk_eq(list_mk_comb(`c981ow_vector`, C981BR_VARS), vtm)];;

(* combine a producer  NPACK /\ IMAGE = fam /\ ooaux .. = S ==> C  with the entry *)
let c981br_lift vtm i prod =
  let e = SPEC_ALL (c981br_entry vtm i) in
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let ooeq = MP e (CONJUNCT2 (CONJUNCT2 h)) in
  let p = SPEC_ALL prod in
  let c = MP p (CONJ (CONJUNCT1 h) (CONJ (CONJUNCT1 (CONJUNCT2 h)) ooeq)) in
  GENL C981BR_VARS (DISCH hyp c);;

let c981br_set vtm i = rand (rand (concl (SPEC_ALL (c981br_entry vtm i))));;

let c981br_in vtm i (x, y) =
  c981br_lift vtm i (c981ow_query_inside i (c981br_set vtm i) (x, y));;

let c981br_out vtm i (x, y) =
  c981br_lift vtm i (c981ow_query_outside i (c981br_set vtm i) (x, y));;

let c981br_apart vtm i j =
  let th = oo_apart `ccc981ri_family` (c981br_mask i) (c981br_mask j) in
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  GENL C981BR_VARS (DISCH hyp (MP (SPEC_ALL th) (CONJ (CONJUNCT1 h) (CONJUNCT1 (CONJUNCT2 h)))));;

(* ~linside (owner i) P from ldisj (owner i) (owner j) and linside (owner j) P *)
let c981br_excl vtm i j (x, y) =
  let ap = SPEC_ALL (c981br_apart vtm i j) and inj = SPEC_ALL (c981br_in vtm j (x, y)) in
  let hyp = C981BR_HYP vtm in
  let d = REWRITE_RULE[ldisj] (MP ap (ASSUME hyp)) in
  let d1 = SPECL [x; y] d and pj = MP inj (ASSUME hyp) in
  let c = REWRITE_RULE[pj] d1 in
  GENL C981BR_VARS (DISCH hyp c);;

let C981BR_ZERO_LT = REAL_ARITH `&1 < l ==> &0 < l`;;

let c981br_close geom owners facts (asl, w as g) =
  let vtm = rand w in
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let side = MATCH_MP OO_SIDE np in
  let side0 = MATCH_MP C981BR_ZERO_LT side in
  let per i = let mt = mk_small_numeral (c981br_mask i) in
              [SPEC mt (MATCH_MP OO_UNIT np); SPEC mt (MATCH_MP OO_BOX np)] in
  let fs = map (fun th -> MP (SPEC_ALL th) h) facts in
  let gth = SPECL (List.concat (map c981br_owner owners)) geom in
  let ths = side :: side0 :: fs @ List.concat (map per owners) in
  (REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   MP_TAC gth THEN REWRITE_TAC ths THEN NO_TAC) g;;

let c981br_prove_excl vtm geom owners facts =
  prove(mk_comb(`c981vd_excludes_vector`, vtm), c981br_close geom owners facts);;

(* representativeVectors[i]! as a literal *)
let c981br_rep_el i =
  (RAND_CONV (REWR_CONV c981vd_representative_vectors) THENC EL_CONV)
    (mk_comb(mk_comb(`EL:num->((num->bool)list)list->(num->bool)list`, mk_small_numeral i),
             `c981vd_representative_vectors`));;

(* |- c981vd_excludes_vector (EL i c981vd_representative_vectors) from a producer on literals *)
let c981br_rep_excluded i prod =
  let e = c981br_rep_el i in
  let th = prod (rand (concl e)) in
  EQ_MP (SYM (AP_TERM `c981vd_excludes_vector` e)) th;;

(* !i. MEM i L ==> c981vd_excludes_vector (EL i c981vd_representative_vectors) *)
let c981br_covered lst ths =
  let ltm = mk_list(map mk_small_numeral lst, `:num`) in
  let goal = mk_forall(`i:num`, mk_imp(mk_comb(mk_comb(`MEM:num->num list->bool`, `i:num`), ltm),
                         `c981vd_excludes_vector (EL i c981vd_representative_vectors)`)) in
  prove(goal, GEN_TAC THEN REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN
              ASM_REWRITE_TAC[] THEN FIRST (map ACCEPT_TAC ths));;

(* ------------------------------------------------------------------------- *)
(* The theorem.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Lean: representative27_excluded *)
let C981BR27_REPRESENTATIVE27_EXCLUDED = c981br_rep_excluded 27 (fun v ->
  c981br_prove_excl v C981R27_IMPOSSIBLE [7; 8; 11]
   [c981br_in v 7 (`&33 / &20`, `&47 / &20`);
    c981br_in v 7 (`&87 / &50`, `&2`);
    c981br_in v 7 (`&8 / &5`, `&3`);
    c981br_in v 8 (`&457 / &500`, `&2`);
    c981br_in v 8 (`&1`, `&12 / &5`);
    c981br_out v 8 (`&1`, `&87 / &50`);
    c981br_in v 11 (`&2`, `&113 / &50`);
    c981br_in v 11 (`&87 / &50`, `&3`);
    c981br_in v 11 (`&12 / &5`, `&3`);
    c981br_apart v 7 8;
    c981br_apart v 7 11]);;
