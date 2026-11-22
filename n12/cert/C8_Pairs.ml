(* ========================================================================= *)
(* W-C898, part 2: the 13 C898 pair steps (Lean Cases/C898/CachedPairs/     *)
(* StepNN, CachedPairPlans.lean: Plan, Plan.contexts, Plan.Check,            *)
(* Plan.sound, StepCover; CachedGeometricPlans.step_sound_of_overlap) and    *)
(* the 927 relaxation links (CompactRelaxation, Bridge/RelaxationTable).     *)
(* Tag C8_ / c8_.                                                            *)
(*                                                                           *)
(*   c8_step_thm "NN" :                                                      *)
(*     |- cr_block_overlap c898_sNN_hdrs (MAP cr_leaf c898_dN)               *)
(*        ==> cr_pair_transition (MAP cr_leaf c898_dS) (MAP cr_leaf c898_dN)  *)
(*                               (MAP cr_leaf c898_dT)                       *)
(* exactly the §4.1 shape: the block-overlap premise is the interface for    *)
(* W-F345 (Lean: the PoseContext.PairCheck fan / common-point families).     *)
(* Step 14 has no plans in Lean (one common point prunes every pair); here   *)
(* each source gets the plan (src, SOME [], []) so its header asks for the   *)
(* overlap of the whole source pose with every neighbour pose.               *)
(* ========================================================================= *)

needs "n12/cert/C8_Data.ml";;
needs "n12/cert/CR_HistStages.ml";;
needs "n12/cert/CH_Stages.ml";;

(* Lean: C898Cached.Plan <source, block, pieces>; the block is stored as its rows
   (Lean blockRows k), the complements are computed (cr_opposite). *)
let c8plan_INDUCT,c8plan_RECURSION = define_type
  "c8plan = C8Plan cpose ((crow list) option) (cpose list)";;
let c8_src = define `c8_src (C8Plan s b ps) = s`;;
let c8_blk = define `c8_blk (C8Plan s b ps) = b`;;
let c8_pieces = define `c8_pieces (C8Plan s b ps) = ps`;;
let c8_header = new_definition `c8_header p = (c8_src p, c8_blk p)`;;

(* Lean: Plan.contexts (outsidePieces complement (blockRows block) (poseRows source)) *)
let c8_contexts = define
 `(c8_contexts src (NONE:(crow list)option) = [cp_rows src]) /\
  (c8_contexts src (SOME b) = cr_outside_pieces b (cp_rows src))`;;

(* Lean: Plan.Check (the complement-row identity is replaced by computing
   cr_opposite; contexts are compared as row lists) *)
let c8_plan_check = define
 `c8_plan_check (C8Plan src blk ps) <=>
    ALL (\ctx. EX (\p. cp_rows p = ctx /\ cp_angle src = cp_angle p) ps) (c8_contexts src blk)`;;

(* Lean: Plan.sound *)
let C8_PLAN_SOUND = prove
 (`forall p c s u v a.
     c8_plan_check p /\ oriented_realizes (cr_leaf (c8_src p)) c s u v a /\
     (forall b. c8_blk p = SOME b ==> ~(forall r. MEM r b ==> cr_holds r (lcx c s u v a) (lcy c s u v a)))
     ==> exists t. MEM t (c8_pieces p) /\ oriented_realizes (cr_leaf t) c s u v a`,
  MATCH_MP_TAC c8plan_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`src:cpose`; `blk:(crow list)option`; `ps:cpose list`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[c8_plan_check; c8_src; c8_blk; c8_pieces] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `exists ctx. MEM ctx (c8_contexts src blk) /\
                      forall r. MEM r ctx ==> cr_holds r (lcx c s u v a) (lcy c s u v a)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`src:cpose`; `c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
      CR_REALIZES_ROWS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `forall b. blk = SOME b ==> ~(forall r. MEM r b ==> cr_holds r (lcx c s u v a) (lcy c s u v a))` THEN
    STRUCT_CASES_TAC(ISPEC `blk:(crow list)option` (cases "option")) THEN
    REWRITE_TAC[c8_contexts; MEM; distinctness "option"; injectivity "option";
                FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; UNWIND_THM1; UNWIND_THM2] THEN
    TRY DISCH_TAC THENL
     [FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; EXISTS_TAC `cp_rows src` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CR_OUTSIDE_PIECES_SOUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `ALL (\ctx. EX (\p. cp_rows p = ctx /\ cp_angle src = cp_angle p) ps)
                   (c8_contexts src blk)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `ctx:crow list`) THEN
  ASM_REWRITE_TAC[GSYM EX_MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:cpose` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:cpose` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CR_TRANSFER THEN EXISTS_TAC `src:cpose` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let c8_plan_ok = new_definition
 `c8_plan_ok (Pd:cpose list) p <=> c8_plan_check p /\ ALL (\t. MEM t Pd) (c8_pieces p)`;;

(* Lean: step_sound / step_sound_of_overlap up to the pieces (StepCover by
   MAP c8_src plans = sources; the overlap premise as cr_block_overlap) *)
let C8_STAGE_SOUND = prove
 (`forall Sd Pd plans Nd.
     MAP c8_src plans = Sd /\ ALL (c8_plan_ok Pd) plans /\
     cr_block_overlap (MAP c8_header plans) Nd
     ==> cr_pair_transition (MAP cr_leaf Sd) Nd (MAP cr_leaf Pd)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cr_block_overlap; cr_pair_transition] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `oriented_pose_covered (MAP cr_leaf Sd) cq sq uq vq aq` THEN
  REWRITE_TAC[oriented_pose_covered; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:pose_leaf` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `src:cpose` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `exists p. MEM p plans /\ c8_src p = src` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (src:cpose) Sd` THEN EXPAND_TAC "Sd" THEN
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `ALL (c8_plan_ok Pd) plans` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `p:c8plan`) THEN ASM_REWRITE_TAC[c8_plan_ok; GSYM ALL_MEM] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`p:c8plan`; `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`]
    C8_PLAN_SOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `blk:crow list` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`src:cpose`; `blk:crow list`] o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhand(snd(strip_forall(concl th))))))) = "MEM"
                       with Failure _ -> false)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `p:c8plan` THEN
      ASM_REWRITE_TAC[c8_header; PAIR_EQ]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                                `ct:real`; `st:real`; `ut:real`; `vt:real`; `aT:real`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:cpose` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_leaf t` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `t:cpose` THEN ASM_MESON_TAC[]);;

(* Lean: link_sound + stepNN_links_checked (pieces -> target domain) *)
let C8_LINKS_COVER = prove
 (`forall Pd Td (L:(cpose#cpose#crhint list)list).
     MAP FST L = Pd /\
     ALL (\l. cr_relax_check (FST l) (FST (SND l)) (SND (SND l)) /\ MEM (FST (SND l)) Td) L
     ==> forall c s u v a. oriented_pose_covered (MAP cr_leaf Pd) c s u v a
                     ==> oriented_pose_covered (MAP cr_leaf Td) c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC CR_RELAX_COVER_SOUND THEN
  MAP_EVERY EXISTS_TAC [`Pd:cpose list`; `L:(cpose#cpose#crhint list)list`] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `src:cpose` THEN EXPAND_TAC "Pd" THEN
  REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:cpose#cpose#crhint list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l:cpose#cpose#crhint list` THEN ASM_SIMP_TAC[]);;

(* The whole step (Lean pairStepNN_geometric_sound) *)
let C8_STEP_THM = prove
 (`forall Sd Pd Td Nd plans hdrs (L:(cpose#cpose#crhint list)list).
     MAP c8_src plans = Sd /\ ALL (c8_plan_ok Pd) plans /\ MAP c8_header plans = hdrs /\
     MAP FST L = Pd /\
     ALL (\l. cr_relax_check (FST l) (FST (SND l)) (SND (SND l)) /\ MEM (FST (SND l)) Td) L
     ==> cr_block_overlap hdrs Nd
     ==> cr_pair_transition (MAP cr_leaf Sd) Nd (MAP cr_leaf Td)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Sd:cpose list`; `Pd:cpose list`; `plans:c8plan list`; `Nd:pose_leaf list`]
    C8_STAGE_SOUND) THEN
  MP_TAC(SPECL [`Pd:cpose list`; `Td:cpose list`; `L:(cpose#cpose#crhint list)list`]
    C8_LINKS_COVER) THEN
  ASM_REWRITE_TAC[cr_pair_transition] THEN MESON_TAC[]);;

let () =
  cr_extra_thms := !cr_extra_thms @
    [c8_src; c8_blk; c8_pieces; c8_contexts; c8_plan_check; cr_outside_pieces; cr_relax_check; EX;
     injectivity "c8plan"];
  cr_cs_reset ();;

(* ---- data ---------------------------------------------------------------- *)

(* links: i src tgt, hints from the oracle *)
let c898_links =
  let hints = Hashtbl.create 1000 in
  List.iter (fun l -> match String.split_on_char '|' l with
      [i; h] -> Hashtbl.replace hints (int_of_string (String.trim i)) (String.trim h)
    | _ -> failwith "link hints") (cr_read_lines "n12/data/cert/c898_link_hints.txt");
  Array.of_list (List.map (fun l -> match cr_split ' ' l with
      [i; s; t] -> (int_of_string s, int_of_string t,
                    Hashtbl.find hints (int_of_string i))
    | _ -> failwith "c898_links") (cr_read_lines "n12/data/cert/c898_links.txt"));;

let c8_link_tm i =
  let (s, t, h) = c898_links.(i) in
  let hs = mk_list (List.map cr_rh_tm (cr_split ';' h), `:crhint`) in
  mk_pair (c8p_tm s, mk_pair (c8p_tm t, hs));;

(* |- cr_relax_check src tgt hints, cached per link index *)
let c8_link_thm_tbl : (int, thm) Hashtbl.t = Hashtbl.create 1000;;

let c8_steps =
  List.map (fun l -> match cr_split ' ' l with
      [st; s; n; t; k] -> (st, s, n, t, int_of_string k)
    | _ -> failwith "c898_steps") (cr_read_lines "n12/data/cert/c898_steps.txt");;

let c8_plan_of_line l =
  match String.split_on_char '|' l with
    [lhs_s; ps] ->
      (match cr_split ' ' lhs_s with
         ["P"; src; b] ->
           let blk = if b = "-" then `NONE:(crow list)option`
                     else mk_comb (`SOME:crow list->(crow list)option`,
                                   c8_rows_tm (List.map int_of_string
                                     (cr_split ',' (String.sub b 2 (String.length b - 2))))) in
           let pieces = mk_list (List.map (fun x -> c8p_tm (int_of_string x)) (cr_split ',' (String.trim ps)), cr_cpose_ty) in
           list_mk_comb (`C8Plan`, [c8p_tm (int_of_string src); blk; pieces])
       | _ -> failwith l)
  | _ -> failwith l;;

let c8_step_tbl : (string, thm) Hashtbl.t = Hashtbl.create 20;;
let c8_hdrs_tbl : (string, thm) Hashtbl.t = Hashtbl.create 20;;

let c8_build_step nd (st, sd, nd_, td, np) =
  let t0 = Unix.gettimeofday () in
  let lines = cr_read_lines (Printf.sprintf "n12/data/cert/c898_plans/S%s.txt" st) in
  let plans = List.map c8_plan_of_line (List.filter (fun l -> l.[0] = 'P') lines) in
  let lk = match List.filter (fun l -> l.[0] = 'L') lines with
      [l] -> List.map int_of_string (cr_split ',' (String.trim (String.sub l 1 (String.length l - 1))))
    | _ -> failwith "links line" in
  if List.length plans <> np then failwith "c8_build_step: plan count";
  let sdef = c8dom_def sd and ndef = c8dom_def nd_ and tdef = c8dom_def td in
  let ltms = List.map c8_link_tm lk in
  (* pieces constant = the link sources, in order (Lean stepNNPieces) *)
  let pieces_tm = mk_list (List.map (fun t -> fst (dest_pair t)) ltms, cr_cpose_ty) in
  let pdef = cr_get_or_define (Printf.sprintf "c898_s%s_pieces" st) pieces_tm in
  let new_links = List.filter (fun i -> not (Hashtbl.mem c8_link_thm_tbl i)) (setify lk) in
  let lgoals = List.map (fun i ->
      let a, b = dest_pair (c8_link_tm i) in let t, h = dest_pair b in
      list_mk_comb (`cr_relax_check`, [a; t; h])) new_links in
  let lchk = cr_parallel_map nd (cr_prove_by_eval []) lgoals in
  List.iter2 (fun i th -> Hashtbl.replace c8_link_thm_tbl i th) new_links lchk;
  let pths = cr_parallel_map nd (fun p -> cr_prove_by_eval [] (mk_comb (`c8_plan_check`, p))) plans in
  let t1 = Unix.gettimeofday () in
  (* plans ok *)
  let pconst = lhs (concl pdef) in
  let ok_thm p chk =
    let tl = PURE_REWRITE_CONV [c8_pieces] (mk_comb (`c8_pieces`, p)) in
    let allm, pred = ch_all_mem pdef (rhs (concl tl)) in
    let allm = EQ_MP (SYM (AP_TERM (mk_comb (`ALL:(cpose->bool)->cpose list->bool`, pred)) tl)) allm in
    MP (ISPECL [pconst; p] (prove(`forall Pd p. c8_plan_check p /\ ALL (\t. MEM t Pd) (c8_pieces p)
                                      ==> c8_plan_ok Pd p`, REWRITE_TAC[c8_plan_ok])))
       (CONJ chk allm) in
  let allp = ch_all_rule (mk_comb (`c8_plan_ok`, pconst)) (List.map2 ok_thm plans pths) in
  let plist = mk_list (plans, `:c8plan`) in
  let msrc = ch_map_eq `c8_src` [c8_src] sdef plist in
  let mh = PURE_REWRITE_CONV [MAP; c8_header; c8_src; c8_blk]
             (mk_icomb (mk_icomb (`MAP:(c8plan->cpose#(crow list)option)->c8plan list->(cpose#(crow list)option)list`,
                                  `c8_header`), plist)) in
  let hdef = cr_get_or_define (Printf.sprintf "c898_s%s_hdrs" st) (rhs (concl mh)) in
  let mh = TRANS mh (SYM hdef) in
  (* links *)
  let lty = `:cpose#cpose#crhint list` in
  let llist = mk_list (ltms, lty) in
  let mfst = TRANS (PURE_REWRITE_CONV [MAP; FST] (mk_icomb (mk_icomb
               (`MAP:(cpose#cpose#crhint list->cpose)->(cpose#cpose#crhint list)list->cpose list`, `FST:cpose#cpose#crhint list->cpose`), llist)))
               (SYM pdef) in
  let tconst = lhs (concl tdef) and tlist = rhs (concl tdef) in
  let lv = mk_var ("l", lty) in
  let lpred = mk_abs (lv, mk_conj (list_mk_comb (`cr_relax_check`,
                  [mk_comb (`FST:cpose#cpose#crhint list->cpose`, lv);
                   mk_comb (`FST:cpose#crhint list->cpose`, mk_comb (`SND:cpose#cpose#crhint list->cpose#crhint list`, lv));
                   mk_comb (`SND:cpose#crhint list->crhint list`, mk_comb (`SND:cpose#cpose#crhint list->cpose#crhint list`, lv))]),
                  mk_icomb (mk_icomb (`MEM:cpose->cpose list->bool`,
                     mk_comb (`FST:cpose#crhint list->cpose`, mk_comb (`SND:cpose#cpose#crhint list->cpose#crhint list`, lv))), tconst))) in
  let lth i tm =
    let (_, (t, _)) = (fun t -> let a, b = dest_pair t in a, dest_pair b) tm in
    let m = cr_mem_rule t tlist in
    let m' = EQ_MP (AP_TERM (mk_comb (`MEM:cpose->cpose list->bool`, t)) (SYM tdef)) m in
    let body = CONJ (Hashtbl.find c8_link_thm_tbl i) m' in
    EQ_MP (SYM ((BETA_CONV THENC PURE_REWRITE_CONV [FST; SND]) (mk_comb (lpred, tm)))) body in
  let alll = ch_all_rule lpred (List.map2 lth lk ltms) in
  let nlist = mk_icomb (mk_icomb (`MAP:(cpose->pose_leaf)->cpose list->pose_leaf list`, `cr_leaf`),
                        lhs (concl ndef)) in
  let th = MP (ISPECL [lhs (concl sdef); pconst; tconst; nlist; plist; lhs (concl hdef); llist] C8_STEP_THM)
              (end_itlist CONJ [msrc; allp; mh; mfst; alll]) in
  Hashtbl.replace c8_step_tbl st th;
  Hashtbl.replace c8_hdrs_tbl st hdef;
  Printf.printf "C898 step %s: %d plans, %d links (%d new), eval %.1fs, assemble %.1fs\n%!" st np
    (List.length lk) (List.length new_links) (t1 -. t0) (Unix.gettimeofday () -. t1);
  th;;

let c8_step_thm st = Hashtbl.find c8_step_tbl st;;
