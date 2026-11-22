(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/ActualOwners.lean    *)
(* (N12Compact.Completion.OtherCases.C976MergedLeft.ActualOwners).  The      *)
(* actual C976 owner map.  Conventions and forward toolkit of                *)
(* CP_OtherCases_C976LeftTop_ActualOwners.ml (family qc qs qu qv qa, unit    *)
(* normals as the hypothesis C976AO_UNIT, the c976ao_ functions).  Data      *)
(* extends C976LeftTop.ActualOwners.Data (c976ao_data) as c976mlao_data.     *)
(* An OpenSquare N is cN sN uN vN aN with cN * cN + sN * sN = &1 /\ &0 < aN. *)
(* UpperBarPoint / TopOnlyLeftPoint.point_original = OCUBP_POINT_ORIGINAL /  *)
(* OCTOLP_POINT_ORIGINAL, C976MergedLeft Input / point = occ976ml_input /    *)
(* OCC976MLM_POINT, mixed_top_advance / top_only_advance =                   *)
(* OCC976MLTT_MIXED_TOP_ADVANCE / OCC976MLTT_TOP_ONLY_ADVANCE.  Tag C976MLAO_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976MergedLeft_Main.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_TopTransfers.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_ActualOwners.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;

(* Lean: Data (structure, extends C976LeftTop.ActualOwners.Data) *)
let C976MLAO_FIELDS =
  [7, `&47 / &20`, `&47 / &20`; 7, `&12 / &5`, `&3`; 3, `&3`, `&3`; 6, `&3`, `&87 / &50`;
   6, `&5 / &2`, `&2`; 10, `&1543 / &500`, `&2`; 10, `&3`, `&113 / &50`; 10, `&3`, `&12 / &5`];;
let c976mlao_data = new_definition
  (mk_eq(list_mk_comb(`c976mlao_data:(num->real)->(num->real)->(num->real)->(num->real)->(num->real)->bool`, C976AO_Q),
    mk_conj(C976AO_DATA, list_mk_conj (map (fun (i, x, y) -> c976ao_in i x y) C976MLAO_FIELDS))));;
let C976MLAO_DATA = list_mk_comb(`c976mlao_data`, C976AO_Q);;
let c976mlao_stmt hyps concl =
  list_mk_forall(C976AO_Q, mk_imp(list_mk_conj ([C976AO_UNIT; C976MLAO_DATA] @ hyps), concl));;
let c976mlao_to_data () = CONJUNCT1 (REWRITE_RULE[c976mlao_data] (ASSUME C976MLAO_DATA));;
let c976mlao_field i x y =
  let tm = c976ao_in i x y in
  find (fun th -> concl th = tm) (CONJUNCTS (CONJUNCT2 (REWRITE_RULE[c976mlao_data] (ASSUME C976MLAO_DATA))));;
(* discharge the base Data hypothesis *)
let c976mlao_fix th = PROVE_HYP (c976mlao_to_data ()) th;;

(* Lean: right_high *)
let c976mlao_right_high () =
  let g = c976mlao_field in
  let t, eqs = c976ao_layers 10 [C976AO_X] in
  c976ao_apply (c976ao_conv eqs) (SPECL t WUMR_POINT)
    [c976ao_punit 10 t; c976ao_pos 10; c976ao_side 10; MATCH_MP LCONT_PULLX (c976ao_box 10);
     g 10 `&1543 / &500` `&2`; g 10 `&3` `&12 / &5`;
     c976ao_excl 10 6 (g 6 `&3` `&87 / &50`); c976ao_excl 10 7 (g 7 `&47 / &20` `&47 / &20`)];;
let C976MLAO_RIGHT_HIGH = c976ao_close (c976mlao_stmt [] (c976ao_in 10 `&3` `&64 / &25`))
  (c976mlao_fix (c976mlao_right_high ()));;

(* Lean: right_bar *)
let c976mlao_right_bar () =
  let lo = `&113 / &50 <= y` and hi = `y <= &64 / &25` in
  GEN `y:real` (DISCH lo (DISCH hi
    (MP (SPECL (c976ao_q 10 @ [`&3`; `&113 / &50`; `&64 / &25`; `y:real`]) OO_VERTICAL_SEGMENT)
       (end_itlist CONJ [c976mlao_field 10 `&3` `&113 / &50`; c976mlao_right_high ();
          c976ao_rr `&113 / &50 < &64 / &25`; ASSUME lo; ASSUME hi]))));;
let C976MLAO_RIGHT_BAR = c976ao_close
  (c976mlao_stmt [] `forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) y`)
  (c976mlao_fix (c976mlao_right_bar ()));;

(* the bar of q 10 excluded from q 7 *)
let c976mlao_bar_excl () =
  let lo = `&113 / &50 <= y` and hi = `y <= &64 / &25` in
  let pt = MP (MP (SPEC `y:real` (c976mlao_right_bar ())) (ASSUME lo)) (ASSUME hi) in
  GEN `y:real` (DISCH lo (DISCH hi (c976ao_excl 7 10 pt)));;
let C976MLAO_MISSING = mk_neg (c976ao_in 7 `&2` `&113 / &50`);;

(* Lean: northeast_sharp *)
let c976mlao_northeast_sharp missing =
  let g = c976mlao_field in
  c976ao_apply ALL_CONV (SPECL (c976ao_q 7) OCUBP_POINT_ORIGINAL)
    [c976ao_unit 7; c976ao_pos 7; c976ao_side 7; g 7 `&47 / &20` `&47 / &20`; g 7 `&12 / &5` `&3`;
     missing; c976ao_excl 7 11 (c976ao_top_origin ()); c976ao_excl 7 3 (g 3 `&3` `&3`);
     c976mlao_bar_excl ()];;
let C976MLAO_NORTHEAST_SHARP = c976ao_close (c976mlao_stmt [C976MLAO_MISSING] (c976ao_in 7 `&101 / &40` `&17 / &8`))
  (c976mlao_fix (c976mlao_northeast_sharp (ASSUME C976MLAO_MISSING)));;

(* Lean: northeast_inward *)
let C976MLAO_NORTHEAST_INWARD =
  let g = c976mlao_field and missing = ASSUME C976MLAO_MISSING in
  c976ao_close (c976mlao_stmt [C976MLAO_MISSING] (c976ao_in 7 `&2` `&131 / &50`))
  (c976mlao_fix (c976ao_apply ALL_CONV (SPECL (c976ao_q 7) OCTOLP_POINT_ORIGINAL)
    [c976ao_unit 7; c976ao_pos 7; c976ao_side 7; g 7 `&47 / &20` `&47 / &20`;
     c976ao_field 7 `&113 / &50` `&3`; c976mlao_northeast_sharp missing; missing;
     c976ao_excl 7 11 (c976ao_top_origin ()); c976ao_excl 7 3 (g 3 `&3` `&3`); c976mlao_bar_excl ()]));;

(* Lean: of_top_advance  (hypotheses C976AO_UNIT, c976ao_data) *)
let C976MLAO_ADVANCE = c976ao_in 11 `&127 / &100` `&3`;;
let c976mlao_of_top_advance advance =
  let f = c976ao_field in
  let t, eqs = C976AO_LEFT in
  let conv = c976ao_conv eqs in
  let lin x y = list_mk_comb(`linside`, t @ [x; y]) in
  let top =
    let lo = `&27 / &100 <= x` and hi = `x <= &37 / &50` in
    let seg = MP (SPECL (c976ao_q 11 @ [`&127 / &100`; `&87 / &50`; `&3`; `&1 + x`]) OO_HORIZONTAL_SEGMENT)
      (end_itlist CONJ [advance; f 11 `&87 / &50` `&3`; c976ao_rr `&127 / &100 < &87 / &50`;
                        c976ao_arith [ASSUME lo] `&127 / &100 <= &1 + x`;
                        c976ao_arith [ASSUME hi] `&1 + x <= &87 / &50`]) in
    GEN `x:real` (DISCH lo (DISCH hi
      (EQ_MP (SYM (conv (mk_neg (lin `x:real` `&1`)))) (c976ao_excl 8 11 seg)))) in
  let segment =
    let lo = `&0 <= t` and hi = `t <= &1` in
    let s = MP (SPECL (c976ao_q 1 @ [`&19 / &25`; `&187 / &100`; `&1`; `&87 / &50`; `t:real`]) C976AO_INSIDE_SEGMENT)
      (end_itlist CONJ [f 1 `&19 / &25` `&187 / &100`; f 1 `&1` `&87 / &50`; ASSUME lo; ASSUME hi]) in
    let px = `--(&6) / &25 + (&6 / &25) * t` and py = `--(&13) / &100 - (&13 / &100) * t` in
    let args = snd (strip_comb (concl s)) in
    let ex = REAL_ARITH (mk_eq(el 5 args, mk_binop `(+):real->real->real` `&1` px))
    and ey = REAL_ARITH (mk_eq(el 6 args, mk_binop `(+):real->real->real` `&2` py)) in
    let s' = EQ_MP (REWRITE_CONV[ex; ey] (concl s)) s in
    GEN `t:real` (DISCH lo (DISCH hi
      (EQ_MP (SYM (c976ao_unfold eqs (mk_neg (lin px py)))) (c976ao_excl 8 1 s')))) in
  let facts = [c976ao_side 8; f 8 `&457 / &500` `&2`; f 8 `&33 / &20` `&47 / &20`; f 8 `&1` `&113 / &50`;
               c976ao_excl 8 5 (f 5 `&3 / &2` `&2`); c976ao_excl 8 4 (f 4 `&1` `&3`)] in
  let tm = list_mk_comb(`occ976ml_input`, t) in
  let body = rhs (concl (REWRITE_CONV[occ976ml_input] tm)) in
  let pf c =
    if is_forall c then find (fun th -> aconv (concl th) c) [top; segment]
    else try find (fun th -> aconv (concl th) c) facts with Failure _ ->
      let e = conv c in
      EQ_MP (SYM e) (find (fun th -> aconv (concl th) (rhs (concl e))) facts) in
  let input = EQ_MP (SYM (REWRITE_CONV[occ976ml_input] tm)) (end_itlist CONJ (map pf (conjuncts body))) in
  let leftPoint = c976ao_apply conv (SPECL t OCC976MLM_POINT) [c976ao_punit 8 t; c976ao_pos 8; input] in
  MP (NOT_ELIM (SPECL [`&127 / &100`; `&49 / &25`] (c976ao_apart 8 5)))
     (CONJ leftPoint (c976ao_southwest_point ()));;
let C976MLAO_OF_TOP_ADVANCE = c976ao_close (c976ao_stmt [C976MLAO_ADVANCE] `false`)
  (c976mlao_of_top_advance (ASSUME C976MLAO_ADVANCE));;

(* Lean: nonnegative_impossible *)
let C976MLAO_N = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`];;
let C976MLAO_NHYPS =
  [`cN * cN + sN * sN = &1`; `&0 < aN`; `aN:real = (qa:num->real) 7`;
   list_mk_forall([`x:real`; `y:real`], mk_eq(list_mk_comb(`linside`, C976MLAO_N @ [`x:real`; `y:real`]),
                                              c976ao_in 7 `x:real` `y:real`));
   `&0 < cN`; `&0 <= sN`; `sN:real <= cN`];;
let C976MLAO_NONNEGATIVE_IMPOSSIBLE =
  let g = c976mlao_field and f = c976ao_field in
  let [nu; npos; shape; inside; cp; sn; order] = map ASSUME C976MLAO_NHYPS in
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV [inside] in
  let nSide = c976ao_arith [shape; c976ao_side 7] `&1 < aN` in
  let wall = let b = REWRITE_RULE[lcont] (c976ao_box 11) in
    GENL [`x:real`; `y:real`] (DISCH (c976ao_in 11 `x:real` `y:real`)
      (c976ao_arith [UNDISCH (SPECL [`x:real`; `y:real`] b)] `y <= &4`)) in
  let disj = EQ_MP (SYM ((REWRITE_CONV[ldisj] THENC conv) (list_mk_comb(`ldisj`, C976MLAO_N @ c976ao_q 11))))
                   (c976ao_apart 7 11) in
  let common = [nu; npos; c976ao_unit 11; c976ao_pos 11; nSide; c976ao_side 11; cp; sn; order; wall; disj] in
  let mixed = c976ao_in 7 `&2` `&113 / &50` in
  let case_mixed =
    let adv = c976ao_apply conv (SPECL (C976MLAO_N @ c976ao_q 11) OCC976MLTT_MIXED_TOP_ADVANCE)
      (common @ [f 7 `&113 / &50` `&3`; ASSUME mixed; c976ao_excl 7 6 (f 6 `&113 / &50` `&2`);
                 f 11 `&2` `&1543 / &500`; f 11 `&8 / &5` `&3`]) in
    c976mlao_of_top_advance adv in
  let case_top =
    let missing = ASSUME (mk_neg mixed) in
    let adv = c976ao_apply conv (SPECL (C976MLAO_N @ c976ao_q 11) OCC976MLTT_TOP_ONLY_ADVANCE)
      (common @ [g 7 `&47 / &20` `&47 / &20`; f 7 `&113 / &50` `&3`; c976mlao_northeast_sharp missing;
                 missing; c976ao_excl 7 3 (g 3 `&3` `&3`); c976mlao_bar_excl (); c976ao_top_origin ()]) in
    let shorter = c976ao_hseg 11 (`&6 / &5`, `&87 / &50`, `&3`, `&127 / &100`) adv (f 11 `&87 / &50` `&3`) in
    c976mlao_of_top_advance shorter in
  c976ao_close
    (list_mk_forall(C976AO_Q @ C976MLAO_N,
       mk_imp(list_mk_conj ([C976AO_UNIT; C976MLAO_DATA] @ C976MLAO_NHYPS), `false`)))
    (c976mlao_fix (DISJ_CASES (SPEC mixed EXCLUDED_MIDDLE) case_mixed case_top));;
