(* ========================================================================= *)
(* Port of Compact/Completion/C981/OutwardRows.lean                          *)
(* (namespace N12Compact.C981CompletionOutwardRows).  Whole original         *)
(* representatives 24, 26 and 39.                                            *)
(* q : Fin 12 -> OpenSquare is the five functions qc qs qu qv qa (unit       *)
(* normals explicit); insidePoints / outsidePoints are the HOL lists         *)
(* c981or_insidePoints / c981or_outsidePoints (EL i, points as real pairs).  *)
(* Transform <true,false,false>.pull (q 9) is the pullSwap square            *)
(* (LINSIDE_PULLSW / LCONT_PULLSW); C981CompletionWallAdvance.point =        *)
(* C981WA_POINT; C981CompletionOutwardAnchor.impossible = C981OA_IMPOSSIBLE; *)
(* inside_segment = OO_HORIZONTAL_SEGMENT.  ExcludesVector =                 *)
(* c981vd_excludes_vector, representativeVectors =                           *)
(* c981vd_representative_vectors (VectorData).  Lean `Check v` quantifies    *)
(* over the computed lists queryInsidePoints / queryOutsidePoints; `excludes *)
(* v checked` is the producer c981or_excludes V (literal V): it applies      *)
(* C981OR_GEOMETRY to the owners and builds every point with c981br_in /     *)
(* c981br_out (Bridge_C981Row27.ml), which fail exactly when a point is not  *)
(* in the query lists, returning |- c981vd_excludes_vector V.  Tag C981OR_.  *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;

(* Lean: insidePoints *)
let c981or_insidePoints = new_definition
 `c981or_insidePoints : ((real#real)list)list =
    [[(&187 / &100, &19 / &25)]; []; [(&3, &1)]; []; [];
     [(&47 / &20, &33 / &20); (&2, &87 / &50); (&3, &8 / &5)]; []; []; [];
     [(&2, &457 / &500); (&12 / &5, &1); (&113 / &50, &1)];
     [(&1543 / &500, &2)]; []]`;;

(* Lean: outsidePoints *)
let c981or_outsidePoints = new_definition
 `c981or_outsidePoints : ((real#real)list)list =
    [[]; []; []; []; []; [(&113 / &50, &2)]; []; []; []; [(&87 / &50, &1)]; []; []]`;;

(* ------------------------------------------------------------------------- *)
(* A small toolkit for geometry theorems over q : Fin 12 -> OpenSquare.      *)
(* ------------------------------------------------------------------------- *)

let c981or_q i = let it = mk_small_numeral i in
  map (fun f -> mk_comb(f, it)) [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let c981or_lt i = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral i) `12`));;

(* hypothesis terms of the geometry theorems, for the point lists L *)
let c981or_hpts neg ltm =
  let body = `linside ((qc:num->real) (i:num)) ((qs:num->real) i) ((qu:num->real) i)
                      ((qv:num->real) i) ((qa:num->real) i) (FST (P:real#real)) (SND P)` in
  let body = if neg then mk_neg body else body in
  mk_forall(`i:num`, mk_imp(`i < 12`, mk_forall(`P:real#real`,
    mk_imp(mk_comb(mk_comb(`MEM:real#real->(real#real)list->bool`, `P:real#real`),
                   mk_comb(mk_comb(`EL:num->((real#real)list)list->(real#real)list`, `i:num`), ltm)),
           body))));;
let C981OR_HUNIT = `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`;;
let C981OR_HSIDE = `forall i. i < 12 ==> &1 < qa i`;;
let C981OR_HBOX = `forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)`;;
let C981OR_HAPART = `forall i j. i < 12 /\ j < 12 /\ ~(i = j)
                     ==> ldisj (qc i) (qs i) (qu i) (qv i) (qa i) (qc j) (qs j) (qu j) (qv j) (qa j)`;;

(* a point of the list (from the assumption of c981or_hpts) *)
let c981or_pt neg ltm ldef i (x, y) =
  let th = MP (SPEC (mk_small_numeral i) (ASSUME (c981or_hpts neg ltm))) (c981or_lt i) in
  let th = SPEC (mk_pair(x, y)) th in
  let mem = EQT_ELIM((REWRITE_CONV[ldef] THENC ONCE_DEPTH_CONV EL_CONV THENC REWRITE_CONV[MEM])
                     (lhand(concl th))) in
  REWRITE_RULE[FST; SND] (MP th mem);;
let c981or_unit i = MP (SPEC (mk_small_numeral i) (ASSUME C981OR_HUNIT)) (c981or_lt i);;
let c981or_side i = MP (SPEC (mk_small_numeral i) (ASSUME C981OR_HSIDE)) (c981or_lt i);;
let c981or_box i = MP (SPEC (mk_small_numeral i) (ASSUME C981OR_HBOX)) (c981or_lt i);;
let c981or_apart i j =
  let ne = EQF_ELIM(NUM_REDUCE_CONV(mk_eq(mk_small_numeral i, mk_small_numeral j))) in
  REWRITE_RULE[ldisj] (MP (SPECL [mk_small_numeral i; mk_small_numeral j] (ASSUME C981OR_HAPART))
                         (CONJ (c981or_lt i) (CONJ (c981or_lt j) ne)));;
(* ~ (q i) at the point of a theorem |- linside (q j) x y *)
let c981or_foreign i j lin =
  let args = snd(strip_comb(concl lin)) in
  let d = SPECL [el 5 args; el 6 args] (c981or_apart i j) in
  let a = lhand(rand(concl d)) in
  NOT_INTRO(DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) lin)));;

(* apply a single-square lemma at a tuple, the premises from the given facts *)
let c981or_apply lemma tuple facts =
  let th = CONV_RULE (REWRITE_CONV[LINSIDE_PULLSW] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
             (SPECL tuple lemma) in
  if not (is_imp (concl th)) then th else
  MP th (TAC_PROOF(([], lhand (concl th)), REPEAT CONJ_TAC THEN
    FIRST [FIRST (map ACCEPT_TAC facts);
           MATCH_MP_TAC LCONT_PULLSW THEN FIRST (map ACCEPT_TAC facts);
           FIRST (map (fun th -> MP_TAC th THEN REAL_ARITH_TAC) facts)]));;

(* Lean: geometry *)
let C981OR_GEOMETRY = prove
 (list_mk_forall([`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`],
   mk_imp(list_mk_conj [C981OR_HUNIT; C981OR_HSIDE; C981OR_HBOX;
                        c981or_hpts false `c981or_insidePoints`;
                        c981or_hpts true `c981or_outsidePoints`; C981OR_HAPART], `false`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let pin = c981or_pt false `c981or_insidePoints` c981or_insidePoints
  and pout = c981or_pt true `c981or_outsidePoints` c981or_outsidePoints in
  let w = [`qs 9:real`; `qc 9:real`; `qu 9:real`; `--qv 9 - qa 9:real`; `qa 9:real`] in
  let reach = c981or_apply C981WA_POINT w
    [MATCH_MP (REAL_ARITH `x + y = &1 ==> y + x = &1`) (c981or_unit 9); c981or_side 9; c981or_box 9;
     pin 9 (`&2`, `&457 / &500`); pin 9 (`&12 / &5`, `&1`); pout 9 (`&87 / &50`, `&1`);
     c981or_foreign 9 0 (pin 0 (`&187 / &100`, `&19 / &25`));
     c981or_foreign 9 5 (pin 5 (`&47 / &20`, `&33 / &20`))] in
  let near = pin 9 (`&113 / &50`, `&1`) in
  SUBGOAL_THEN `forall z. &113 / &50 <= z /\ z <= &14 / &5 ==> ~linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) z (&1)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) z (&1)` ASSUME_TAC THENL
     [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN
      ASM_REWRITE_TAC[near; reach] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPECL [`z:real`; `&1`] (c981or_apart 5 9)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (c981or_q 5) C981OA_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         FIRST (map ACCEPT_TAC
          [c981or_unit 5; c981or_side 5;
           pin 5 (`&47 / &20`, `&33 / &20`); pin 5 (`&2`, `&87 / &50`); pin 5 (`&3`, `&8 / &5`);
           c981or_foreign 5 2 (pin 2 (`&3`, `&1`));
           c981or_foreign 5 10 (pin 10 (`&1543 / &500`, `&2`));
           pout 5 (`&113 / &50`, `&2`)]);
         MP_TAC (c981or_side 5) THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* excludes: the geometry at the owners of a literal vector.                 *)
(* ------------------------------------------------------------------------- *)

(* prove c981vd_excludes_vector V from a geometry theorem G (premises as in
   C981OR_GEOMETRY, plus optional extra premises closed by `extra`) *)
let c981or_excludes_with geom inside insdef outside outdef extra vtm =
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let pts prod l = List.concat (map (fun (i, ps) -> map (fun p -> MP (SPEC_ALL (prod vtm i p)) h) ps) l) in
  let ins = pts c981br_in inside and outs = pts c981br_out outside in
  let f s = mk_abs(`i:num`, list_mk_comb(s, C981BR_VARS @ [`EL i c981ow_masks`])) in
  let gth = SPECL [f `ooc`; f `oos`; f `oou`; f `oov`; mk_abs(`i:num`, `l:real`)] geom in
  let expand defs =
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC(defs @ [c981ow_masks]) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[MEM; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM;
                FORALL_UNWIND_THM2; FST; SND] in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC gth THEN BETA_TAC THEN
    REPEAT CONJ_TAC THEN
    FIRST ([GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OO_UNIT THEN ACCEPT_TAC np;
            GEN_TAC THEN DISCH_TAC THEN ACCEPT_TAC (MATCH_MP OO_SIDE np);
            GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OO_BOX THEN ACCEPT_TAC np;
            expand [insdef] THEN REWRITE_TAC ins THEN NO_TAC;
            expand [outdef] THEN REWRITE_TAC outs THEN NO_TAC;
            REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN
            EXISTS_TAC `ccc981ri_family` THEN ASM_REWRITE_TAC[C981OW_LENGTH] THEN
            REWRITE_TAC[c981ow_masks] THEN REWRITE_TAC[fst C981OW_LIST; snd C981OW_LIST] THEN NO_TAC]
           @ extra));;

let c981or_inside_list =
  [0, [(`&187 / &100`, `&19 / &25`)]; 2, [(`&3`, `&1`)];
   5, [(`&47 / &20`, `&33 / &20`); (`&2`, `&87 / &50`); (`&3`, `&8 / &5`)];
   9, [(`&2`, `&457 / &500`); (`&12 / &5`, `&1`); (`&113 / &50`, `&1`)];
   10, [(`&1543 / &500`, `&2`)]];;
let c981or_outside_list = [5, [(`&113 / &50`, `&2`)]; 9, [(`&87 / &50`, `&1`)]];;

(* Lean: Check, excludes *)
let c981or_excludes vtm =
  c981or_excludes_with C981OR_GEOMETRY c981or_inside_list c981or_insidePoints
    c981or_outside_list c981or_outsidePoints [] vtm;;

(* Lean: coveredIds *)
let c981or_coveredIds = new_definition
 `c981or_coveredIds = [24; 26; 39]`;;

(* Lean: checked *)
let C981OR_CHECKED = map (fun i -> c981br_rep_excluded i c981or_excludes) [24; 26; 39];;

(* Lean: covered_excluded *)
let C981OR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981or_coveredIds] (c981br_covered [24; 26; 39] C981OR_CHECKED);;
