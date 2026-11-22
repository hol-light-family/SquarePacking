(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/OriginalData.lean.           *)
(* Literal original-owner entrance boundary for the C1090 proof.            *)
(* (Lean header: "Source only, uncompiled.")                                 *)
(* Lean  owners p i = owner p (masks i)  is the owner 5-tuple at mask        *)
(*   EL i c1090od_masks;  as a family q : Fin 12 -> OpenSquare (the form of *)
(* Early.Input, c1090eg_input) it is the five coordinate functions           *)
(*   qc = \i. ooc c1 c2 a b l (EL i c1090od_masks), ..., qa = \i. l          *)
(* (c1090od_owners below).                                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1090_EarlyGeometry.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family, masks *)
let c1090od_family = new_definition
 `c1090od_family = {1,12,48,192,256,512,1024,2048,4098,8192,16384,32768}`;;
let c1090od_masks = new_definition
 `c1090od_masks = [1;12;48;192;256;512;1024;2048;4098;8192;16384;32768]`;;
let C1090OD_F = `c1090od_family`;;
let C1090OD_MASKS = [1;12;48;192;256;512;1024;2048;4098;8192;16384;32768];;

(* Lean: owners, as the five coordinate functions *)
let c1090od_owners = map (fun f -> mk_abs(`i:num`, list_mk_comb(f,
    [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `EL i c1090od_masks`])))
  [`ooc`; `oos`; `oou`; `oov`] @ [`\i:num. (l:real)`];;

let C1090OD_LIST = oo_list_facts C1090OD_F (rand (concl c1090od_masks));;
let C1090OD_LENGTH = (REWRITE_CONV[c1090od_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c1090od_masks`;;

(* Lean: mask_member (private) *)
let C1090OD_MASK_MEMBER = prove
 (`forall i. i < 12 ==> EL i c1090od_masks IN c1090od_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C1090OD_LENGTH; c1090od_masks] THEN ASM_REWRITE_TAC[fst C1090OD_LIST]);;

(* Lean: masks_injective (private) *)
let C1090OD_MASKS_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c1090od_masks = EL j c1090od_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c1090od_masks` THEN ASM_REWRITE_TAC[C1090OD_LENGTH] THEN
  REWRITE_TAC[c1090od_masks; snd C1090OD_LIST]);;

(* apart of two owners of the list (used by early_input) *)
let C1090OD_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c1090od_masks)) (oos c1 c2 a b l (EL i c1090od_masks))
               (oou c1 c2 a b l (EL i c1090od_masks)) (oov c1 c2 a b l (EL i c1090od_masks)) l
               (ooc c1 c2 a b l (EL j c1090od_masks)) (oos c1 c2 a b l (EL j c1090od_masks))
               (oou c1 c2 a b l (EL j c1090od_masks)) (oov c1 c2 a b l (EL j c1090od_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c1090od_family` THEN
  ASM_REWRITE_TAC[C1090OD_LENGTH] THEN REWRITE_TAC[c1090od_masks] THEN
  REWRITE_TAC[fst C1090OD_LIST; snd C1090OD_LIST]);;

(* Lean: AuxiliaryEntrance (structure) *)
let c1090od_auxent = new_definition
 `c1090od_auxent (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&87 / &50) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&12 / &5) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&113 / &50) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&12 / &5) /\
    (linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&1) \/
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) \/
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5)) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50)) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5)) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)) /\
    (linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3) \/
     (linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3) /\ linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)))`;;

(* Lean: seed — a producer: owner (masks i) contains the seed point (x, y)
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = c1090od_family ==> linside (owner m_i) x y *)
let c1090od_seed i (x, y) = oo_inst C1090OD_F (oo_seed (el i C1090OD_MASKS) (x, y));;

(* Lean: marker1_owned  (owners p 8 = owner 4098) *)
let C1090OD_MARKER1_OWNED = c1090od_seed 8 (`&457 / &500`, `&1`);;

(* Lean: marker1_omitted_by_singleton  (owners p 0 = owner 1, marker 1 = (457/500, 1)) *)
let C1090OD_MARKER1_OMITTED_BY_SINGLETON = oo_inst C1090OD_F (oo_missing 1 1);;

let C1090OD_EL_CONV = REWRITE_CONV[c1090od_masks] THENC ONCE_DEPTH_CONV EL_CONV;;

(* Lean: early_input *)
let C1090OD_EARLY_INPUT =
  let [qc; qs; qu; qv; qa] = c1090od_owners in
  let ent = list_mk_comb(`c1090od_auxent`, c1090od_owners)
  and inp = list_mk_comb(`c1090eg_input`, c1090od_owners) in
  let seeds = [c1090od_seed 0 (`&28 / &25`, `&1`);
     c1090od_seed 0 (`&87 / &50`, `&1`);
     c1090od_seed 0 (`&187 / &100`, `&19 / &25`);
     c1090od_seed 1 (`&3`, `&457 / &500`);
     c1090od_seed 1 (`&1543 / &500`, `&1`);
     c1090od_seed 1 (`&3`, `&1`);
     c1090od_seed 2 (`&3`, `&3`);
     c1090od_seed 3 (`&1`, `&1543 / &500`);
     c1090od_seed 3 (`&1`, `&3`);
     c1090od_seed 4 (`&33 / &20`, `&33 / &20`);
     c1090od_seed 5 (`&47 / &20`, `&33 / &20`);
     c1090od_seed 6 (`&47 / &20`, `&47 / &20`);
     c1090od_seed 7 (`&33 / &20`, `&47 / &20`);
     c1090od_seed 8 (`&457 / &500`, `&1`);
     c1090od_seed 8 (`&457 / &500`, `&2`);
     c1090od_seed 9 (`&2`, `&457 / &500`);
     c1090od_seed 10 (`&1543 / &500`, `&2`);
     c1090od_seed 11 (`&2`, `&1543 / &500`)] in
  prove
   (list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(mk_conj(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family`, ent), inp)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = ent)) THEN
    DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS o CONV_RULE C1090OD_EL_CONV o BETA_RULE o
                REWRITE_RULE[c1090od_auxent]) THEN
    REWRITE_TAC[c1090eg_input] THEN BETA_TAC THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [GEN_TAC THEN DISCH_TAC THEN MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
      CONV_TAC C1090OD_EL_CONV THEN ASM_SIMP_TAC seeds THEN NO_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                     `i:num`; `j:num`] C1090OD_APART) THEN
      ASM_REWRITE_TAC[ldisj] THEN NO_TAC]);;

