(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C974/Entrance.lean                 *)
(* (namespace N12Compact.Completion.OtherCases.C974.OriginalData).  Actual   *)
(* C974 compulsory auxiliaries.  owners p i / actual p i are written with    *)
(* the literal mask of index i (EL i c974od_masks: 5->256, 6->512, 7->1024,  *)
(* 8->4096, 9->8192, 10->16384, 11->32768).  The structure Compulsory is the *)
(* predicate c974e_compulsory.  dom / foreignAux are OO_DOMAIN_CASES_TAC /   *)
(* OO_EXCLUDE_ALL_TAC on the C974Domains domains (the C975FiniteCuts and     *)
(* Domains.northeast_cut / top_cut cuts are re-evaluated on the same allowed *)
(* lists); aux = oo_aux_point.  Tag C974E_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C974_OriginalData.ml";;
needs "n12/geometry/CP_OtherCases_C974_Domains.ml";;

let c974e_p m (x, y) =
  let mt = mk_small_numeral m in
  list_mk_comb(`linside`, map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`;
     `b:num->real`; `l:real`; mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; x; y]);;

(* Lean: Compulsory (structure) *)
let c974e_compulsory = new_definition (mk_eq(
  `(c974e_compulsory:(num->real)->(num->real)->(num->real)->(num->real)->real->bool) c1 c2 a b l`,
  list_mk_conj
   [c974e_p 256 (`&2`, `&87 / &50`);
    c974e_p 256 (`&87 / &50`, `&2`);
    c974e_p 512 (`&3`, `&87 / &50`);
    mk_disj(c974e_p 512 (`&113 / &50`, `&2`), c974e_p 512 (`&3`, `&8 / &5`));
    mk_disj(c974e_p 1024 (`&2`, `&113 / &50`), c974e_p 1024 (`&12 / &5`, `&3`));
    mk_disj(c974e_p 1024 (`&113 / &50`, `&2`), c974e_p 1024 (`&113 / &50`, `&3`));
    c974e_p 4096 (`&1`, `&113 / &50`);
    c974e_p 4096 (`&1`, `&12 / &5`);
    c974e_p 8192 (`&12 / &5`, `&1`);
    c974e_p 8192 (`&113 / &50`, `&1`);
    c974e_p 16384 (`&3`, `&113 / &50`);
    c974e_p 16384 (`&3`, `&12 / &5`);
    mk_disj(c974e_p 32768 (`&113 / &50`, `&3`),
            mk_conj(c974e_p 32768 (`&8 / &5`, `&3`), c974e_p 32768 (`&87 / &50`, `&3`)))]));;

let C974E_DOMS = [1, C974D_SOUTHWEST; 2, C974D_LEFT_SINGLETON; 8192, C974D_BOTTOM;
                  256, C974D_SOUTHWEST_CENTRAL; 4096, C974D_LEFT; 512, C974D_SOUTHEAST;
                  16384, C974D_RIGHT; 1024, C974D_NORTHEAST; 32768, C974D_TOP];;

(* Lean: compulsory *)
let C974E_COMPULSORY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family
     ==> c974e_compulsory c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
                (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
                (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
                (4 IN ooaux c1 c2 a b l 256 /\ 13 IN ooaux c1 c2 a b l 256) /\
                (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096)`
    STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C974D_F C974E_DOMS
      [1, [2; 12]; 2, [0; 10]; 8192, [6; 15]; 256, [4; 13]; 4096, [1; 11]];
    ALL_TAC] THEN
  SUBGOAL_THEN `8 IN ooaux c1 c2 a b l 512 /\
                (16 IN ooaux c1 c2 a b l 512 \/ 18 IN ooaux c1 c2 a b l 512)`
    (CONJUNCTS_THEN ASSUME_TAC) THENL
   [OO_EXCLUDE_ALL_TAC C974D_F 512 THEN OO_DOMAIN_CASES_TAC C974D_SOUTHEAST; ALL_TAC] THEN
  SUBGOAL_THEN `9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384`
    STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C974D_F C974E_DOMS [16384, [9; 19]]; ALL_TAC] THEN
  SUBGOAL_THEN `(5 IN ooaux c1 c2 a b l 1024 \/ 7 IN ooaux c1 c2 a b l 1024) /\
                (16 IN ooaux c1 c2 a b l 1024 \/ 17 IN ooaux c1 c2 a b l 1024)`
    ASSUME_TAC THENL
   [OO_EXCLUDE_ALL_TAC C974D_F 1024 THEN OO_DOMAIN_CASES_TAC C974D_NORTHEAST; ALL_TAC] THEN
  SUBGOAL_THEN `17 IN ooaux c1 c2 a b l 32768 \/
                (3 IN ooaux c1 c2 a b l 32768 /\ 14 IN ooaux c1 c2 a b l 32768)`
    ASSUME_TAC THENL
   [OO_DOMAIN_CASES_TAC C974D_TOP; ALL_TAC] THEN
  REWRITE_TAC[c974e_compulsory] THEN
  REWRITE_TAC (map oo_aux_point [4; 13; 8; 16; 18; 5; 7; 17; 1; 11; 6; 15; 9; 19; 3; 14]) THEN
  ASM_REWRITE_TAC[]);;
