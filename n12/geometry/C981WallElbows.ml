(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981WallElbows.lean                               *)
(* (namespace N12Compact.C981WallElbows).  Original C981 exclusions from     *)
(* both opposite elbow squares and their actual four wall neighbours.        *)
(* Conventions of Bridge_C981Row27.ml (c981br_* toolkit): owners p i is the  *)
(* OriginalOwners owner at mask EL i c981ow_masks; ExcludesVector is         *)
(* c981vd_excludes_vector.  transform 0 = <false,false,true> is pullY        *)
(* (Transform.apply (x,y) = (x, 4 - y)), transform 1 = <false,true,false> is *)
(* pullX ((x,y) -> (4 - x, y)); pullY (c,s,u,v,a) = (c,--s,u - 4s,4c - v - a,a),*)
(* pullX (c,s,u,v,a) = (--c,s,u - 4c,--v - a - 4s,a) (p2_base LINSIDE_PULLX/Y).*)
(* Check v quantifies over the computed lists queryInsidePoints /            *)
(* queryOutsidePoints; as in CC_C981_Ownership.ml it is checked at a literal *)
(* vector by the producers c981ow_query_inside / _outside (c981we_check);    *)
(* center and excludes are producers at a literal vector satisfying Check    *)
(* (they fail exactly when the Lean decide would).  CentralWallCenter.point  *)
(* is CWC_POINT.  Tag C981WE_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/CentralWallCenter.ml";;

(* Lean: transform *)
let c981we_transform = new_definition
 `c981we_transform : (bool#bool#bool)list = [(false,false,true); (false,true,false)]`;;

(* Lean: roles *)
let c981we_roles = new_definition
 `c981we_roles : (num list)list = [[5; 10; 9]; [7; 8; 11]]`;;
let C981WE_ROLES = [[5; 10; 9]; [7; 8; 11]];;

(* Lean: insidePoints, outsidePoints *)
let c981we_inside_points = new_definition
 `c981we_inside_points : ((real#real)list)list =
    [[(&2, &113 / &50); (&113 / &50, &2); (&47 / &20, &47 / &20)];
     [(&1543 / &500, &2); (&3, &12 / &5)];
     [(&2, &1543 / &500); (&12 / &5, &3)]]`;;
let c981we_outside_points = new_definition
 `c981we_outside_points : ((real#real)list)list =
    [[(&47 / &20, &33 / &20); (&33 / &20, &47 / &20)];
     [(&3, &87 / &50)];
     [(&87 / &50, &3)]]`;;

let C981WE_INSIDE =
  map (map (fun t -> let a, b = dest_pair t in (a, b)) o dest_list)
    (dest_list (rhs (concl c981we_inside_points)));;
let C981WE_OUTSIDE =
  map (map (fun t -> let a, b = dest_pair t in (a, b)) o dest_list)
    (dest_list (rhs (concl c981we_outside_points)));;

(* Transform.applyRat on literal points *)
let c981we_apply i (x, y) =
  let four_minus t = rand (concl (REAL_RAT_REDUCE_CONV (mk_binop `(-):real->real->real` `&4` t))) in
  if i = 0 then (x, four_minus y) else (four_minus x, y);;

(* ------------------------------------------------------------------------- *)
(* The pulled squares.                                                       *)
(* ------------------------------------------------------------------------- *)

let C981WE_LDISJ_PULLY = prove
 (`forall cA sA uA vA aA cB sB uB vB aB. ldisj cA sA uA vA aA cB sB uB vB aB
     ==> ldisj cA (--sA) (uA - &4 * sA) (&4 * cA - vA - aA) aA
               cB (--sB) (uB - &4 * sB) (&4 * cB - vB - aB) aB`,
  REWRITE_TAC[ldisj; LINSIDE_PULLY] THEN MESON_TAC[]);;

let C981WE_LDISJ_PULLX = prove
 (`forall cA sA uA vA aA cB sB uB vB aB. ldisj cA sA uA vA aA cB sB uB vB aB
     ==> ldisj (--cA) sA (uA - &4 * cA) (--vA - aA - &4 * sA) aA
               (--cB) sB (uB - &4 * cB) (--vB - aB - &4 * sB) aB`,
  REWRITE_TAC[ldisj; LINSIDE_PULLX] THEN MESON_TAC[]);;

(* CentralWallCenter.point for the pullY images of three squares A, R, T,
   stated for the original squares at the transformed points *)
let C981WE_POINT_Y = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aR /\ aA = aT /\
     lcont cR sR uR vR aR /\ lcont cT sT uT vT aT /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&8 / &5) /\
     ~linside cR sR uR vR aR (&3) (&113 / &50) /\
     linside cT sT uT vT aT (&2) (&457 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&1) /\
     ~linside cT sT uT vT aT (&87 / &50) (&1) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `--sA:real`; `uA - &4 * sA`; `&4 * cA - vA - aA`; `aA:real`;
                `cR:real`; `--sR:real`; `uR - &4 * sR`; `&4 * cR - vR - aR`; `aR:real`;
                `cT:real`; `--sT:real`; `uT - &4 * sT`; `&4 * cT - vT - aT`; `aT:real`]
    CWC_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLY; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC LCONT_PULLY THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC C981WE_LDISJ_PULLY THEN FIRST_ASSUM ACCEPT_TAC]);;

let C981WE_POINT_X = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aR /\ aA = aT /\
     lcont cR sR uR vR aR /\ lcont cT sT uT vT aT /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&457 / &500) (&2) /\
     linside cR sR uR vR aR (&1) (&12 / &5) /\
     ~linside cR sR uR vR aR (&1) (&87 / &50) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&8 / &5) (&3) /\
     ~linside cT sT uT vT aT (&113 / &50) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--cA:real`; `sA:real`; `uA - &4 * cA`; `--vA - aA - &4 * sA`; `aA:real`;
                `--cR:real`; `sR:real`; `uR - &4 * cR`; `--vR - aR - &4 * sR`; `aR:real`;
                `--cT:real`; `sT:real`; `uT - &4 * cT`; `--vT - aT - &4 * sT`; `aT:real`]
    CWC_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLX; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC LCONT_PULLX THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC C981WE_LDISJ_PULLX THEN FIRST_ASSUM ACCEPT_TAC]);;

let C981WE_POINT = [| C981WE_POINT_Y; C981WE_POINT_X |];;

(* ------------------------------------------------------------------------- *)
(* Check and the packing-level statements (producers at a literal vector).   *)
(* ------------------------------------------------------------------------- *)

(* the query facts of Check v for transform i, in the order of C981WE_POINT *)
let c981we_facts vtm i =
  let roles = el i C981WE_ROLES in
  let ins j = map (fun p -> c981br_in vtm (el j roles) (c981we_apply i p)) (el j C981WE_INSIDE) in
  let outs j = map (fun p -> c981br_out vtm (el j roles) (c981we_apply i p)) (el j C981WE_OUTSIDE) in
  ins 0 @ outs 0 @ ins 1 @ outs 1 @ ins 2 @ outs 2;;

(* Lean: Check (decided at a literal vector; raises Failure when Check fails) *)
let c981we_check vtm =
  (try ignore (c981we_facts vtm 0); ignore (c981we_facts vtm 1); true with Failure _ -> false);;

(* Lean: center  |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = ccc981ri_family /\
                    c981ow_vector c1 c2 a b l = v ==> linside (owners p (roles i 0)) 2 2 *)
let c981we_center vtm i =
  let roles = el i C981WE_ROLES in
  let r0 = el 0 roles and r1 = el 1 roles and r2 = el 2 roles in
  let facts = c981we_facts vtm i @ [c981br_apart vtm r0 r1; c981br_apart vtm r0 r2] in
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let side = MATCH_MP OO_SIDE np in
  let side0 = MATCH_MP C981BR_ZERO_LT side in
  let per r = let mt = mk_small_numeral (c981br_mask r) in
              [SPEC mt (MATCH_MP OO_UNIT np); SPEC mt (MATCH_MP OO_BOX np)] in
  let fs = map (fun th -> MP (SPEC_ALL th) h) facts in
  let gth = SPECL (List.concat (map c981br_owner roles)) C981WE_POINT.(i) in
  let ths = side :: side0 :: fs @ List.concat (map per roles) in
  let concl0 = list_mk_comb(`linside`, c981br_owner r0 @ [`&2`; `&2`]) in
  prove(list_mk_forall(C981BR_VARS, mk_imp(hyp, concl0)),
        REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC gth THEN REWRITE_TAC ths);;

(* Lean: excludes *)
let c981we_excludes vtm =
  let se = c981we_center vtm 0 and nw = c981we_center vtm 1 in
  let ap = c981br_apart vtm 5 7 in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(UNDISCH (SPEC_ALL ap)) THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&2`]) THEN
    REWRITE_TAC[UNDISCH (SPEC_ALL se); UNDISCH (SPEC_ALL nw)]);;

(* Lean: coveredIds *)
let c981we_covered_ids = new_definition
 `c981we_covered_ids = [0; 7; 8; 19; 22; 44; 50; 52; 53; 66; 110; 111; 113; 114; 115; 116]`;;
let C981WE_COVERED = [0; 7; 8; 19; 22; 44; 50; 52; 53; 66; 110; 111; 113; 114; 115; 116];;

(* Lean: covered_count *)
let C981WE_COVERED_COUNT = prove
 (`LENGTH c981we_covered_ids = 16`,
  REWRITE_TAC[c981we_covered_ids; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: covered_checked  (Check holds at every covered representative) *)
let C981WE_COVERED_CHECKED =
  List.for_all (fun i -> c981we_check (rand (concl (c981br_rep_el i)))) C981WE_COVERED;;
if not C981WE_COVERED_CHECKED then failwith "C981WE: covered_checked fails";;

(* Lean: covered_excluded *)
let C981WE_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981we_covered_ids]
    (c981br_covered C981WE_COVERED (map (fun i -> c981br_rep_excluded i c981we_excludes) C981WE_COVERED));;
