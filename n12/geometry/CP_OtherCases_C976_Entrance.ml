(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976/Entrance.lean                  *)
(* (namespace N12Compact.Completion.OtherCases.C976.OriginalData).          *)
(* Authentic original-family compulsory points.  owners p i is the owner of *)
(* mask EL i c976od_masks = [1;2;12;48;192;256;512;1024;6144;8192;16384;    *)
(* 32768]; the covers / right_pair / top_component / left_f1_of_g1 are the  *)
(* C976D_* theorems, apart is OO_APART, singleton_* are C976OD_SINGLETON_*.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976_Domains.ml";;

let c976e_in m (x, y) = c976d_in m (x, y);;
let c976e_q s = parse_term ("(" ^ s ^ "):real");;

(* Lean: Compulsory (structure) *)
let c976e_compulsory = new_definition (mk_eq(
  `(c976e_compulsory:(num->real)->(num->real)->(num->real)->(num->real)->real->bool) c1 c2 a b l`,
  let p m x y = c976e_in m (c976e_q x, c976e_q y) in
  list_mk_conj
   [p 256 "&2" "&87 / &50";
    p 256 "&87 / &50" "&2";
    p 512 "&3" "&87 / &50";
    mk_disj(p 512 "&113 / &50" "&2", p 512 "&3" "&8 / &5");
    mk_disj(p 1024 "&2" "&113 / &50", p 1024 "&12 / &5" "&3");
    mk_disj(p 1024 "&113 / &50" "&2", p 1024 "&113 / &50" "&3");
    p 6144 "&1" "&113 / &50";
    p 6144 "&1" "&12 / &5";
    p 8192 "&12 / &5" "&1";
    p 8192 "&113 / &50" "&1";
    p 16384 "&3" "&113 / &50";
    p 16384 "&3" "&12 / &5";
    mk_disj(p 32768 "&113 / &50" "&3",
            mk_conj(p 32768 "&8 / &5" "&3", p 32768 "&87 / &50" "&3"))]));;

(* a contradiction from two distinct owners containing the same point *)
let C976E_CLASH_TAC (asl, w as g) =
  let owned = List.filter_map (fun (_, th) ->
     let t = concl th in
     try let f, args = strip_comb t in
         if f <> `linside` then failwith "" else
         let m = dest_small_numeral (rand (hd args)) in
         Some (m, (el 5 args, el 6 args), th)
     with _ -> None) asl in
  let pairs = flat (map (fun (m, p, th) -> List.filter_map (fun (n, q, th') ->
     if m < n && aconv (fst p) (fst q) && aconv (snd p) (snd q) then Some (m, n, p) else None) owned)
     owned) in
  if pairs = [] then failwith "C976E_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  let fam = `c976od_family` in
  (MP_TAC(SPECL [x; y] (REWRITE_RULE[ldisj]
     (MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 fam; mk_small_numeral m; mk_small_numeral n] OO_APART)
         (end_itlist CONJ [ASSUME `NPACK c1 c2 a b l`;
                           ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c976od_family`;
                           in_fam m fam; in_fam n fam;
                           EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n)))]))))
   THEN ASM_REWRITE_TAC[]) g;;

(* prove an owned point from a disjunctive theorem: every other disjunct clashes *)
let C976E_COVER_TAC th =
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)] THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN TRY(DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
  C976E_CLASH_TAC;;

let C976E_ADD tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: compulsory *)
let C976E_COMPULSORY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> c976e_compulsory c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let p m x y = c976e_in m (c976e_q x, c976e_q y) in
  let sv y = MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                            `l:real`; c976e_q y] C976OD_SINGLETON_VERTICAL) THEN
             ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC
  and sh x = MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                            `l:real`; c976e_q x] C976OD_SINGLETON_HORIZONTAL) THEN
             ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC in
  sv "&87 / &50" THEN sv "&8 / &5" THEN sh "&8 / &5" THEN sh "&87 / &50" THEN
  C976E_ADD (p 256 "&2" "&87 / &50") (C976E_COVER_TAC C976D_SOUTHWEST_F_COVER) THEN
  C976E_ADD (p 256 "&87 / &50" "&2") (C976E_COVER_TAC C976D_SOUTHWEST_G_COVER) THEN
  C976E_ADD (p 8192 "&12 / &5" "&1") (C976E_COVER_TAC C976D_BOTTOM_F_COVER) THEN
  C976E_ADD (p 8192 "&113 / &50" "&1") (C976E_COVER_TAC C976D_BOTTOM_G_COVER) THEN
  C976E_ADD (p 512 "&3" "&87 / &50") (C976E_COVER_TAC C976D_SOUTHEAST_F_COVER) THEN
  C976E_ADD (mk_neg(p 16384 "&3" "&87 / &50")) (DISCH_TAC THEN C976E_CLASH_TAC) THEN
  C976E_ADD (mk_conj(p 16384 "&3" "&113 / &50", p 16384 "&3" "&12 / &5"))
    (MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
       C976D_RIGHT_PAIR) THEN ASM_REWRITE_TAC[]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  C976E_ADD (p 6144 "&1" "&12 / &5") (C976E_COVER_TAC C976D_LEFT_G_COVER) THEN
  C976E_ADD (p 6144 "&1" "&113 / &50")
    (MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
       C976D_LEFT_F1_OF_G1) THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[c976e_compulsory] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [C976E_COVER_TAC C976D_SOUTHEAST_G_COVER;
    C976E_COVER_TAC C976D_NORTHEAST_F_COVER;
    C976E_COVER_TAC C976D_NORTHEAST_G_COVER;
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
       C976D_TOP_COMPONENT) THEN ASM_REWRITE_TAC[]]);;
