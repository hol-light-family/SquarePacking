(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C972Entrance.lean                 *)
(* (namespace N12Compact.FiniteCases.C972).  The actual C972 compulsory      *)
(* entrance.  actual p i / owners p i are written with the literal mask of   *)
(* index i (EL i c972o_masks: 0->1, 1->2, 5->256, 6->512, 7->1024, 9->4096,  *)
(* 10->8192, 11->16384): ooaux c1 c2 a b l m and the owner 5-tuple of m.    *)
(* Structures Compulsory / Points are c972e_compulsory / c972e_points.       *)
(* foreign_aux is applied inside OO_EXCLUDE_ALL_TAC; the C975FiniteCuts and  *)
(* C972Domains.northeast_cut cuts are re-evaluated by OO_DOMAIN_CASES_TAC on *)
(* the C972Domains domains (same allowed lists); aux = oo_aux_point.         *)
(* Tag C972E_.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972Owners.ml";;

(* Lean: Compulsory (structure) *)
let c972e_compulsory = new_definition
 `c972e_compulsory (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    (2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
    (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
    (4 IN ooaux c1 c2 a b l 256 /\ 13 IN ooaux c1 c2 a b l 256) /\
    (8 IN ooaux c1 c2 a b l 512 /\
     (16 IN ooaux c1 c2 a b l 512 \/ 18 IN ooaux c1 c2 a b l 512)) /\
    ((5 IN ooaux c1 c2 a b l 1024 \/ 7 IN ooaux c1 c2 a b l 1024) /\
     (16 IN ooaux c1 c2 a b l 1024 \/ 17 IN ooaux c1 c2 a b l 1024)) /\
    (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096) /\
    (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
    (9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384)`;;

let C972E_DOMS = [1, C972D_SOUTHWEST; 2, C972D_LEFT_SINGLETON; 8192, C972D_BOTTOM;
                  256, C972D_SOUTHWEST_CENTRAL; 4096, C972D_LEFT; 512, C972D_SOUTHEAST;
                  16384, C972D_RIGHT; 1024, C972D_NORTHEAST];;

(* Lean: compulsory *)
let C972E_COMPULSORY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> c972e_compulsory c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
                (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
                (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
                (4 IN ooaux c1 c2 a b l 256 /\ 13 IN ooaux c1 c2 a b l 256) /\
                (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096)`
    STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C972D_F C972E_DOMS
      [1, [2; 12]; 2, [0; 10]; 8192, [6; 15]; 256, [4; 13]; 4096, [1; 11]];
    ALL_TAC] THEN
  SUBGOAL_THEN `8 IN ooaux c1 c2 a b l 512 /\
                (16 IN ooaux c1 c2 a b l 512 \/ 18 IN ooaux c1 c2 a b l 512)`
    (CONJUNCTS_THEN ASSUME_TAC) THENL
   [OO_EXCLUDE_ALL_TAC C972D_F 512 THEN OO_DOMAIN_CASES_TAC C972D_SOUTHEAST; ALL_TAC] THEN
  SUBGOAL_THEN `9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384`
    STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C972D_F C972E_DOMS [16384, [9; 19]]; ALL_TAC] THEN
  SUBGOAL_THEN `(5 IN ooaux c1 c2 a b l 1024 \/ 7 IN ooaux c1 c2 a b l 1024) /\
                (16 IN ooaux c1 c2 a b l 1024 \/ 17 IN ooaux c1 c2 a b l 1024)`
    ASSUME_TAC THENL
   [OO_EXCLUDE_ALL_TAC C972D_F 1024 THEN OO_DOMAIN_CASES_TAC C972D_NORTHEAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[c972e_compulsory]);;

let c972e_p m (x, y) =
  let mt = mk_small_numeral m in
  list_mk_comb(`linside`, map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`;
     `b:num->real`; `l:real`; mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; x; y]);;

(* Lean: Points (structure) *)
let c972e_points = new_definition (mk_eq(
  `(c972e_points:(num->real)->(num->real)->(num->real)->(num->real)->real->bool) c1 c2 a b l`,
  list_mk_conj
   [c972e_p 256 (`&2`, `&87 / &50`);
    c972e_p 256 (`&87 / &50`, `&2`);
    c972e_p 512 (`&3`, `&87 / &50`);
    mk_disj(c972e_p 512 (`&113 / &50`, `&2`), c972e_p 512 (`&3`, `&8 / &5`));
    mk_disj(c972e_p 1024 (`&2`, `&113 / &50`), c972e_p 1024 (`&12 / &5`, `&3`));
    mk_disj(c972e_p 1024 (`&113 / &50`, `&2`), c972e_p 1024 (`&113 / &50`, `&3`));
    c972e_p 4096 (`&1`, `&113 / &50`);
    c972e_p 4096 (`&1`, `&12 / &5`);
    c972e_p 8192 (`&12 / &5`, `&1`);
    c972e_p 8192 (`&113 / &50`, `&1`);
    c972e_p 16384 (`&3`, `&113 / &50`);
    c972e_p 16384 (`&3`, `&12 / &5`)]));;

(* Lean: points *)
let C972E_POINTS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> c972e_points c1 c2 a b l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C972E_COMPULSORY) THEN
  REWRITE_TAC[c972e_compulsory; c972e_points] THEN
  REWRITE_TAC (map oo_aux_point [4; 13; 8; 16; 18; 5; 7; 17; 1; 11; 6; 15; 9; 19]) THEN
  MESON_TAC[]);;
