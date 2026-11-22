(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/OriginalData.lean             *)
(* (namespace N12Compact.Completion.OtherCases.C1089.OriginalData).          *)
(* The literal original C1089 owners.  family / masks = SingletonCorner's    *)
(* c1089sc_family / c1089sc_masks; Lean owners p i = owner p (masks i) is    *)
(* the owner 5-tuple at mask EL i c1089sc_masks.                             *)
(* q : Fin 12 -> OpenSquare is qc qs qu qv qa : num -> real (i < 12), as in  *)
(* CP_OtherCases_C1091_EntranceFrame.ml; owners p is c1089od_owners:         *)
(* qc = \i. ooc c1 c2 a b l (EL i c1089sc_masks), ..., qa = \i. l.           *)
(* The structure Frame is c1089od_frame.  Tag C1089OD_.                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_SingletonCorner.ml";;

let C1089OD_LIST = oo_list_facts `c1089sc_family` (rand (concl c1089sc_masks));;
let C1089OD_LENGTH = (REWRITE_CONV[c1089sc_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c1089sc_masks`;;

(* Lean: mask_member *)
let C1089OD_MASK_MEMBER = prove
 (`forall i. i < 12 ==> EL i c1089sc_masks IN c1089sc_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C1089OD_LENGTH; c1089sc_masks] THEN ASM_REWRITE_TAC[fst C1089OD_LIST]);;

(* Lean: masks_injective *)
let C1089OD_MASKS_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c1089sc_masks = EL j c1089sc_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c1089sc_masks` THEN ASM_REWRITE_TAC[C1089OD_LENGTH] THEN
  REWRITE_TAC[c1089sc_masks; snd C1089OD_LIST]);;

(* Lean: seed — a producer at a literal index i and seed point (x, y):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = c1089sc_family ==> linside (owner m_i) x y *)
let c1089od_seed i (x, y) = oo_inst `c1089sc_family` (oo_seed (el i C1089SC_MASKS) (x, y));;

(* the apartness of two listed owners *)
let C1089OD_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c1089sc_masks)) (oos c1 c2 a b l (EL i c1089sc_masks))
               (oou c1 c2 a b l (EL i c1089sc_masks)) (oov c1 c2 a b l (EL i c1089sc_masks)) l
               (ooc c1 c2 a b l (EL j c1089sc_masks)) (oos c1 c2 a b l (EL j c1089sc_masks))
               (oou c1 c2 a b l (EL j c1089sc_masks)) (oov c1 c2 a b l (EL j c1089sc_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c1089sc_family` THEN
  ASM_REWRITE_TAC[C1089OD_LENGTH] THEN REWRITE_TAC[c1089sc_masks] THEN
  REWRITE_TAC[fst C1089OD_LIST; snd C1089OD_LIST]);;

(* Lean: Frame (structure) *)
let c1089od_frame = new_definition
 `c1089od_frame (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    (forall i. i < 12 ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) (&457 / &500) (&1)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&457 / &500) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&187 / &100) (&19 / &25) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&457 / &500) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&1543 / &500) (&1) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&1543 / &500) (&3) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&1543 / &500) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&1543 / &500) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&457 / &500) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500)`;;

(* Lean: owners (abbrev SingletonCorner.owners), as coordinate functions *)
let c1089od_owners = map (fun f -> mk_abs(`i:num`, list_mk_comb(f,
    [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `EL i c1089sc_masks`])))
  [`ooc`; `oos`; `oou`; `oov`] @ [`\i:num. (l:real)`];;

let C1089OD_EL_CONV = REWRITE_CONV[c1089sc_masks] THENC ONCE_DEPTH_CONV EL_CONV;;

(* Lean: frame *)
let C1089OD_FRAME =
  let fr = list_mk_comb(`c1089od_frame`, c1089od_owners) in
  let seeds = map (fun (i, p) -> c1089od_seed i p)
    [0, (`&1`, `&457 / &500`); 0, (`&28 / &25`, `&1`); 0, (`&87 / &50`, `&1`);
     0, (`&187 / &100`, `&19 / &25`);
     1, (`&3`, `&457 / &500`); 1, (`&1543 / &500`, `&1`); 1, (`&3`, `&1`);
     2, (`&1543 / &500`, `&3`); 2, (`&3`, `&1543 / &500`); 2, (`&3`, `&3`);
     3, (`&1`, `&1543 / &500`); 3, (`&457 / &500`, `&3`); 3, (`&1`, `&3`);
     4, (`&33 / &20`, `&33 / &20`); 5, (`&47 / &20`, `&33 / &20`);
     6, (`&47 / &20`, `&47 / &20`); 7, (`&33 / &20`, `&47 / &20`);
     8, (`&457 / &500`, `&2`); 9, (`&2`, `&457 / &500`);
     10, (`&1543 / &500`, `&2`); 11, (`&2`, `&1543 / &500`)] in
  prove
   (list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family`, fr)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[c1089od_frame] THEN BETA_TAC THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [GEN_TAC THEN DISCH_TAC THEN MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
      MP_TAC (SPEC_ALL C1089SC_ABSENT_MARKER) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      CONV_TAC C1089OD_EL_CONV THEN ASM_SIMP_TAC seeds THEN NO_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                     `i:num`; `j:num`] C1089OD_APART) THEN
      ASM_REWRITE_TAC[ldisj] THEN NO_TAC]);;
