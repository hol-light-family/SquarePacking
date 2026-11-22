(* ========================================================================= *)
(* W-CHORD, part 3: data, evaluation and assembly of the 20 historical      *)
(* chord stages and of the C713 height stage (design §4.4).                 *)
(*   ck_chord_thm (case, step) :                                             *)
(*     |- ch_chord_transition (MAP cr_leaf hCK_dA_v) (MAP cr_leaf hCK_dN1)   *)
(*          (MAP cr_leaf hCK_dN2) (MAP cr_leaf hCK_dN3) (MAP cr_leaf hCK_dA_w) *)
(*   (Lean Preservation.Chords.CKStepNN.sound; masks: ck_chord_masks).       *)
(*   C713_HEIGHT (Lean C713ChordDirect.source_to_after_height, square level) *)
(* Data: n12/data/cert/chord_{radii,stages}.txt, n12/data/cert/chord_plans/,         *)
(*       n12/data/cert/c713_height{,_hints}.txt                                  *)
(*       (n12/scripts/cert_extract_chord.py, n12/scripts/cert_oracle_height.py).     *)
(* ========================================================================= *)

needs "n12/cert/CR_HistStages.ml";;
needs "n12/cert/CH_Height.ml";;

let CH_PLAN_OK_INTRO = prove
 (`forall W Td p. ch_plan_check W p /\ ALL (\t. MEM t Td) (ch_plan_targets p) ==> ch_plan_ok W Td p`,
  REWRITE_TAC[ch_plan_ok]);;

let CH_HEIGHT_OK_INTRO = prove
 (`forall Td h. ch_height_check h /\ ALL (\t. MEM t Td) (chh_targets h) ==> ch_height_ok Td h`,
  REWRITE_TAC[ch_height_ok]);;

(* ---- parsing ------------------------------------------------------------ *)

let ch_row_tm s = match cr_split ',' s with
    [x; y; c; st] -> cr_row_of_strings (x, y, c, st = "1")
  | _ -> failwith ("ch_row_tm " ^ s);;

let ch_hints_tm s =
  mk_list (List.map cr_rh_tm (cr_split ';' (String.trim s)), `:crhint`);;

let ch_terms_tm s =
  mk_list (List.map (fun t -> match String.split_on_char '@' t with
      [w; i] -> mk_pair (cr_int_tm w, mk_small_numeral (int_of_string i))
    | _ -> failwith "ch_terms_tm") (cr_split ',' (String.trim s)), `:int#num`);;

let ch_nums_tm s =
  mk_list (List.map (fun i -> mk_small_numeral (int_of_string i)) (cr_split ',' (String.trim s)), `:num`);;

let ch_branch_tm s =
  let s = String.trim s in
  let i = String.index s ':' in
  let hd = String.trim (String.sub s 0 i) and tl = String.sub s (i + 1) (String.length s - i - 1) in
  match cr_split ' ' hd with
    ["K"; t] -> (mk_comb (mk_comb (`ChKeep`, hp_tm (int_of_string t)), ch_hints_tm tl), Some (int_of_string t))
  | ["C"; ins] -> (mk_comb (mk_comb (`ChClose`, ch_nums_tm ins), ch_terms_tm tl), None)
  | _ -> failwith ("ch_branch_tm " ^ s);;

let ch_num k = mk_small_numeral (int_of_string k);;

type ch_rec = Chrecn of int * term | Chrecp of term;;

let ch_record_of_line l =
  match String.split_on_char '|' l with
    [lhs_s; hs] when l.[0] = 'N' ->
      (match cr_split ' ' lhs_s with
         ["N"; c; src; k; rl; rh] ->
           Chrecn (int_of_string c,
               list_mk_comb (`ChNbr`, [hp_tm (int_of_string src); ch_num k; ch_row_tm rl;
                                       ch_row_tm rh; ch_hints_tm hs]))
       | _ -> failwith l)
  | [lhs_s; bl; bh] when l.[0] = 'P' ->
      (match cr_split ' ' lhs_s with
         ["P"; src; k; cl; chr] ->
           let (blt, _) = ch_branch_tm bl and (bht, _) = ch_branch_tm bh in
           Chrecp (list_mk_comb (`ChPlan`, [hp_tm (int_of_string src); ch_num k; ch_row_tm cl;
                                        ch_row_tm chr; blt; bht]))
       | _ -> failwith l)
  | _ -> failwith ("chord record: " ^ l);;

(* case step hz ln ld hn hd sdom tdom n1 n2 n3 masks nplans nnbrs *)
let ch_stages =
  List.map (fun l -> match cr_split ' ' l with
      [c; st; hz; ln; ld; hn; hd; sd; td; n1; n2; n3; m; np; nn] ->
        (c, st, hz = "1", (ln, ld, hn, hd), sd, td, [n1; n2; n3],
         List.map int_of_string (cr_split ',' m), int_of_string np, int_of_string nn)
    | _ -> failwith "chord_stages") (cr_read_lines "n12/data/cert/chord_stages.txt");;

let ck_chord_masks : (string * string, int list) Hashtbl.t = Hashtbl.create 30;;
let () = List.iter (fun (c, st, _, _, _, _, _, m, _, _) -> Hashtbl.replace ck_chord_masks (c, st) m) ch_stages;;

(* ---- structural helpers ------------------------------------------------- *)

let ch_all_rule pred ths =
  itlist (fun th acc ->
      let x = rand (concl th) and t = rand (concl acc) in
      MP (ISPECL [pred; x; t] CR_ALL_CONS) (CONJ th acc))
    ths (ISPEC pred CR_ALL_NIL);;

(* |- ALL (\t. MEM t Tc) l  for a literal list l of members of the literal Tdef rhs *)
let ch_all_mem tdef l =
  let tconst = lhs (concl tdef) and tlist = rhs (concl tdef) in
  let ty = `:cpose` in
  let tv = mk_var ("t", ty) in
  let pred = mk_abs (tv, mk_icomb (mk_icomb (`MEM:cpose->cpose list->bool`, tv), tconst)) in
  let mem x =
    let m = cr_mem_rule x tlist in
    let m' = EQ_MP (AP_TERM (mk_comb (`MEM:cpose->cpose list->bool`, x)) (SYM tdef)) m in
    EQ_MP (SYM (BETA_CONV (mk_comb (pred, x)))) m' in
  ch_all_rule pred (List.map mem (dest_list l)), pred;;

(* |- MAP f l = C  where C's definition has the rhs MAP f l evaluated *)
let ch_map_eq f defs dth l =
  let ty = type_of l in
  let elt = hd (snd (dest_type ty)) in
  let rty = hd (snd (dest_type (type_of (rhs (concl dth))))) in
  let mapc = mk_const ("MAP", [elt, aty; rty, bty]) in
  let th = PURE_REWRITE_CONV (MAP :: defs) (mk_comb (mk_comb (mapc, f), l)) in
  TRANS th (SYM dth);;

(* ---- chord stages ------------------------------------------------------- *)

let ck_chord_tbl : (string * string, thm) Hashtbl.t = Hashtbl.create 30;;
let ck_chord_time : (string * string, float * float) Hashtbl.t = Hashtbl.create 30;;

let ch_win_tm hz (ln, ld, hn, hd) =
  list_mk_comb (`ChWin`, [if hz then `true` else `false`; cr_int_tm ln; cr_int_tm ld; cr_int_tm hn; cr_int_tm hd]);;

let ch_eval_thm tm = cr_prove_by_eval [] tm;;

let ck_build_chord nd (c, st, hz, q, sd, td, nds, _, np, nn) =
  let t0 = Unix.gettimeofday () in
  let recs = List.map ch_record_of_line
               (cr_read_lines (Printf.sprintf "n12/data/cert/chord_plans/C%s_S%s.txt" c st)) in
  let w = ch_win_tm hz q in
  let nb k = List.concat (List.map (function Chrecn (j, t) when j = k -> [t] | _ -> []) recs) in
  let plans = List.concat (List.map (function Chrecp t -> [t] | _ -> []) recs) in
  let n1 = nb 0 and n2 = nb 1 and n3 = nb 2 in
  if List.length plans <> np || List.length n1 + List.length n2 + List.length n3 <> nn then
    failwith "ck_build_chord: record counts";
  let sdef = hdom_def (c, sd) and tdef = hdom_def (c, td) in
  let ndefs = List.map (fun d -> hdom_def (c, d)) nds in
  let nchk = mk_comb (`ch_nbr_check`, w) and pchk = mk_comb (`ch_plan_check`, w) in
  let items = List.map (fun t -> mk_comb (nchk, t)) (n1 @ n2 @ n3) @
              List.map (fun t -> mk_comb (pchk, t)) plans in
  let ths = cr_parallel_map nd ch_eval_thm items in
  let t1 = Unix.gettimeofday () in
  let rec split k l = if k = 0 then [], l else match l with
      h :: t -> let a, b = split (k - 1) t in h :: a, b | [] -> failwith "split" in
  let th1, rest = split (List.length n1) ths in
  let th2, rest = split (List.length n2) rest in
  let th3, pths = split (List.length n3) rest in
  let all_n ths = ch_all_rule nchk ths in
  let tconst = lhs (concl tdef) in
  let okpred = list_mk_comb (`ch_plan_ok`, [w; tconst]) in
  let ok_thm p chk =
    let tl = PURE_REWRITE_CONV [ch_plan_targets; ch_branch_targets; APPEND]
               (mk_comb (`ch_plan_targets`, p)) in
    let allm, pred = ch_all_mem tdef (rhs (concl tl)) in
    let allm = EQ_MP (SYM (AP_TERM (mk_comb (`ALL:(cpose->bool)->cpose list->bool`, pred)) tl)) allm in
    MP (ISPECL [w; tconst; p] CH_PLAN_OK_INTRO) (CONJ chk allm) in
  let oks = List.map2 ok_thm plans pths in
  let allp = ch_all_rule okpred oks in
  let plist = mk_list (plans, `:chplan`) in
  let msrc = ch_map_eq `chp_src` [chp_src] sdef plist in
  let mn l d = ch_map_eq `chn_src` [chn_src] d (mk_list (l, `:chnbr`)) in
  let [d1; d2; d3] = ndefs in
  let th = MP (ISPECL [w; mk_list (n1, `:chnbr`); mk_list (n2, `:chnbr`); mk_list (n3, `:chnbr`);
                       plist; lhs (concl sdef); tconst;
                       lhs (concl d1); lhs (concl d2); lhs (concl d3)] CH_STAGE_THM)
             (end_itlist CONJ [all_n th1; all_n th2; all_n th3; allp; msrc;
                               mn n1 d1; mn n2 d2; mn n3 d3]) in
  let t2 = Unix.gettimeofday () in
  Hashtbl.replace ck_chord_tbl (c, st) th;
  Hashtbl.replace ck_chord_time (c, st) (t1 -. t0, t2 -. t1);
  Printf.printf "chord C%s S%s: %d plans, %d neighbours, eval %.1fs, assemble %.1fs\n%!" c st
    np nn (t1 -. t0) (t2 -. t1);
  th;;

let ck_chord_thm (c, st) = Hashtbl.find ck_chord_tbl (c, st);;

(* ---- C713 height -------------------------------------------------------- *)

let ch_bhint_tm s =
  if String.length s > 2 && String.sub s 0 2 = "d:" then
    mk_comb (`BhDirect`, cr_rh_tm (String.sub s 2 (String.length s - 2)))
  else match String.split_on_char ':' s with
      ["i"; ins; terms] -> mk_comb (mk_comb (`BhImpossible`, ch_nums_tm ins), ch_terms_tm terms)
    | _ -> failwith ("ch_bhint_tm " ^ s);;

let ch_height_records () =
  let hints = Hashtbl.create 200 in
  List.iter (fun l -> match String.split_on_char '|' l with
      [i; h] -> Hashtbl.replace hints (int_of_string (String.trim i))
                  (List.map ch_bhint_tm (cr_split ';' (String.trim h)))
    | _ -> failwith "height hints") (cr_read_lines "n12/data/cert/c713_height_hints.txt");
  List.map (fun l -> match cr_split ' ' l with
      [i; src; cut; tgt; _; _; _; _; k] ->
        if int_of_string k < 0 then failwith "height radius not in table";
        let tg = if tgt = "-" then `NONE:cpose option`
                 else mk_comb (`SOME:cpose->cpose option`, hp_tm (int_of_string tgt)) in
        list_mk_comb (`ChHeight`, [hp_tm (int_of_string src); ch_row_tm cut; tg; ch_num k;
                                    mk_list (Hashtbl.find hints (int_of_string i), `:cbhint`)])
    | _ -> failwith "height record") (cr_read_lines "n12/data/cert/c713_height.txt");;

let ch_build_height nd =
  let t0 = Unix.gettimeofday () in
  let recs = ch_height_records () in
  let sdef = hdom_def ("713", "7_0") and tdef = hdom_def ("713", "7_6") in
  let ths = cr_parallel_map nd ch_eval_thm (List.map (fun t -> mk_comb (`ch_height_check`, t)) recs) in
  let t1 = Unix.gettimeofday () in
  let tconst = lhs (concl tdef) in
  let ok_thm h chk =
    let tl = PURE_REWRITE_CONV [chh_targets; ch_opt_list] (mk_comb (`chh_targets`, h)) in
    let allm, pred = ch_all_mem tdef (rhs (concl tl)) in
    let allm = EQ_MP (SYM (AP_TERM (mk_comb (`ALL:(cpose->bool)->cpose list->bool`, pred)) tl)) allm in
    MP (ISPECL [tconst; h] CH_HEIGHT_OK_INTRO) (CONJ chk allm) in
  let allh = ch_all_rule (mk_comb (`ch_height_ok`, tconst)) (List.map2 ok_thm recs ths) in
  let hl = mk_list (recs, `:chheight`) in
  let msrc = ch_map_eq `chh_src` [chh_src] sdef hl in
  let th = MP (ISPECL [hl; lhs (concl sdef); tconst] CH_HEIGHT_STAGE) (CONJ allh msrc) in
  Printf.printf "C713 height: %d records, eval %.1fs, assemble %.1fs\n%!" (List.length recs)
    (t1 -. t0) (Unix.gettimeofday () -. t1);
  th;;

(* the square-level statement of design §4.4 with three explicit neighbours *)
let CH_HEIGHT_EXPLICIT = prove
 (`forall Sd Td.
   (forall c s u v a (cN:num->real) sN uN vN aN.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) (&87 / &50)) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\ linside (cN i) (sN i) (uN i) (vN i) (aN i) x y)) /\
     oriented_pose_covered Sd c s u v a
     ==> oriented_pose_covered Td c s u v a)
   ==> forall c s u v a c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     c1 * c1 + s1 * s1 = &1 /\ &0 < a1 /\ c2 * c2 + s2 * s2 = &1 /\ &0 < a2 /\
     c3 * c3 + s3 * s3 = &1 /\ &0 < a3 /\
     ldisj c s u v a c1 s1 u1 v1 a1 /\ ldisj c s u v a c2 s2 u2 v2 a2 /\
     ldisj c s u v a c3 s3 u3 v3 a3 /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c1 s1 u1 v1 a1 (&1) (&87 / &50) /\ linside c2 s2 u2 v2 a2 (&2) (&87 / &50) /\
     linside c3 s3 u3 v3 a3 (&3) (&87 / &50) /\
     oriented_pose_covered Sd c s u v a
     ==> oriented_pose_covered Td c s u v a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
    `ch_fam c1 c2 c3 c3`; `ch_fam s1 s2 s3 s3`; `ch_fam u1 u2 u3 u3`; `ch_fam v1 v2 v3 v3`;
    `ch_fam a1 a2 a3 a3`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `i < 3 <=> i = 0 \/ i = 1 \/ i = 2`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[ch_fam; ARITH_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[CH_LINSIDE_CLOSED]);;
