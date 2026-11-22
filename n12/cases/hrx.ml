(* ========================================================================= *)
(* The six HighRight(Extra) cases 678, 680, 690, 691, 694, 711 (Jatloe:      *)
(* Compact/Cases/FourSquareHighRight{,Extra}/CaseN.lean): domain_cases_sound *)
(* over the certified domains; every consistent assignment is closed either  *)
(* by the HighRight template (FourSquareCaseHighRight) or by an owner        *)
(* segment crossing (Bridge/OwnerSegmentCrossing, data Cases/                *)
(* FourSquareHighRight/Crossings.lean).  Result: HRX_CASE_THMS.              *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/bridge_ext.ml";;
needs "n12/geometry/hr_data.ml";;
needs "n12/geometry/FourSquareHighRight.ml";;

(* Lean: OwnerSegmentCrossing.impossible, for one checked crossing datum:
   the point (1-t) P0 + t P1 = (1-w) Q0 + w Q1 lies in both squares *)
let osc_lemma (p0, p1, q0, q1, t, w) =
  let r x = term_of_rat (nlin_rat x) in
  let pt (x, y) = (r x, r y) in
  let (x0, y0) = pt p0 and (x1, y1) = pt p1 and (x2, y2) = pt q0 and (x3, y3) = pt q1 in
  let tq = nlin_rat t and wq = nlin_rat w in
  let one = num 1 in
  if tq </ num 0 || tq >/ one || wq </ num 0 || wq >/ one then failwith "osc_lemma: weights" else
  let cx = (one -/ tq) */ rat_of_term x0 +/ tq */ rat_of_term x1
  and cy = (one -/ tq) */ rat_of_term y0 +/ tq */ rat_of_term y1 in
  if cx <>/ (one -/ wq) */ rat_of_term x2 +/ wq */ rat_of_term x3 ||
     cy <>/ (one -/ wq) */ rat_of_term y2 +/ wq */ rat_of_term y3 then failwith "osc_lemma: no crossing" else
  let x = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
  and y = [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] in
  let li q (px, py) = list_mk_comb(`linside`, q @ [px; py]) in
  let tm = list_mk_forall(x @ y, mk_imp(list_mk_conj
             [li x (x0, y0); li x (x1, y1); li y (x2, y2); li y (x3, y3);
              list_mk_comb(`ldisj`, x @ y)], `false`)) in
  prove(tm, REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [term_of_rat cx; term_of_rat cy]) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Crossings.lean *)
let HRX_CROSSINGS = [
  (0, (512, 17408, [8;16], [5;18], ("47/20","33/20"), ("3","87/50"), ("47/20","47/20"), ("3","8/5"), "5/6", "5/6"));
  (1, (2048, 33792, [5;14], [3;16], ("33/20","47/20"), ("87/50","3"), ("47/20","47/20"), ("8/5","3"), "5/6", "5/6"));
  (2, (512, 34816, [8;16], [3;18], ("47/20","33/20"), ("3","87/50"), ("33/20","47/20"), ("3","8/5"), "20/29", "74/87"));
  (3, (17408, 34816, [5;14], [3;16], ("47/20","47/20"), ("2","113/50"), ("2","1543/500"), ("113/50","2"), "9437/20175", "2891/4035"));
  (4, (256, 6144, [4;13], [1;18], ("33/20","33/20"), ("87/50","2"), ("457/500","2"), ("3","8/5"), "4357/7661", "2891/7661"));
  (5, (256, 6144, [4;13], [1;16], ("33/20","33/20"), ("87/50","2"), ("457/500","2"), ("113/50","2"), "1", "413/673"));
  (6, (512, 8448, [4;15], [6;13], ("47/20","33/20"), ("113/50","1"), ("33/20","33/20"), ("12/5","1"), "5/6", "5/6"))];;
let HRX_CROSSING_RECIPES = map (fun (k, (m1, m2, o1, o2, p0, p1, q0, q1, t, w)) ->
    (k, (osc_lemma (p0, p1, q0, q1, t, w), (false, false, false), [m1; m2], [o1; o2]))) HRX_CROSSINGS;;

(* crossings used by each case (Lean case files) *)
let HRX_USES = [(678, [0]); (680, [1]); (690, [0]); (691, [2; 0; 3]); (694, [4; 0; 5]); (711, [6; 1])];;

let hrx_case_thm (cid, fam, doms, trf, masks, owned, lb, rb) =
  let (mk, _) = chop_list 4 masks and (ok, _) = chop_list 4 owned in
  let recipes = (FSHR_IMPOSSIBLE, trf, mk, ok) ::
                map (fun k -> assoc k HRX_CROSSING_RECIPES) (assoc cid HRX_USES) in
  gen_enum_thm (xdfun None) [] recipes (cid, fam, map (fun (m, d) -> (m, Xd d)) doms);;

let HRX_CASE_THMS = map check_case_thm
  (run_cases "HIGHRIGHT-SPLIT" hrx_case_thm (fun (cid,_,_,_,_,_,_,_) -> cid)
     (filter (fun (cid,_,_,_,_,_,_,_) -> mem cid (map fst HRX_USES))
        (VAR_FourSquareHighRight @ VAR_FourSquareHighRightExtra)));;
