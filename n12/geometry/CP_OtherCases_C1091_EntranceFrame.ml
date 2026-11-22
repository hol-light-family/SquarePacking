(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/EntranceFrame.lean.          *)
(* Actual C1091 points used by the continuous entrance.                     *)
(* q : Fin 12 -> OpenSquare is  qc qs qu qv qa : num -> real (i < 12); the   *)
(* packing's  owners p  is  c1091ef_owners:  qc = \i. ooc c1 c2 a b l (EL i  *)
(* c1091od_masks), ..., qa = \i. l.  The structure Frame is c1091ef_frame.   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_EntranceDomains.ml";;

(* Lean: Frame (structure) *)
let c1091ef_frame = new_definition
 `c1091ef_frame (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
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
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&1) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500)`;;

let c1091ef_owners = map (fun f -> mk_abs(`i:num`, list_mk_comb(f,
    [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `EL i c1091od_masks`])))
  [`ooc`; `oos`; `oou`; `oov`] @ [`\i:num. (l:real)`];;

let C1091EF_EL_CONV = REWRITE_CONV[c1091od_masks] THENC ONCE_DEPTH_CONV EL_CONV;;

(* Lean: frame *)
let C1091EF_FRAME =
  let fr = list_mk_comb(`c1091ef_frame`, c1091ef_owners) in
  let seeds = [c1091od_seed 0 (`&1`, `&457 / &500`);
     c1091od_seed 0 (`&28 / &25`, `&1`);
     c1091od_seed 0 (`&87 / &50`, `&1`);
     c1091od_seed 0 (`&187 / &100`, `&19 / &25`);
     c1091od_seed 1 (`&3`, `&457 / &500`);
     c1091od_seed 1 (`&1543 / &500`, `&1`);
     c1091od_seed 1 (`&3`, `&1`);
     c1091od_seed 2 (`&1543 / &500`, `&3`);
     c1091od_seed 2 (`&3`, `&1543 / &500`);
     c1091od_seed 2 (`&3`, `&3`);
     c1091od_seed 3 (`&1`, `&1543 / &500`);
     c1091od_seed 3 (`&1`, `&3`);
     c1091od_seed 4 (`&457 / &500`, `&1`);
     c1091od_seed 4 (`&33 / &20`, `&33 / &20`);
     c1091od_seed 5 (`&47 / &20`, `&33 / &20`);
     c1091od_seed 6 (`&47 / &20`, `&47 / &20`);
     c1091od_seed 7 (`&33 / &20`, `&47 / &20`);
     c1091od_seed 8 (`&457 / &500`, `&2`);
     c1091od_seed 9 (`&2`, `&457 / &500`);
     c1091od_seed 10 (`&1543 / &500`, `&2`);
     c1091od_seed 11 (`&2`, `&1543 / &500`)] in
  prove
   (list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`, fr)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[c1091ef_frame] THEN BETA_TAC THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [GEN_TAC THEN DISCH_TAC THEN MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
      CONV_TAC C1091EF_EL_CONV THEN ASM_SIMP_TAC (OC1091EML_ORIGINAL :: seeds) THEN NO_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                     `i:num`; `j:num`] C1091OD_APART) THEN
      ASM_REWRITE_TAC[ldisj] THEN NO_TAC]);;

