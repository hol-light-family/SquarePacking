(* ========================================================================= *)
(* W-ASM (n12/docs/cert_design.md §4.5, §9): case composition of the seven       *)
(* certificate cases 701, 713, 717, 973, 978, 979 and 898.                   *)
(*                                                                           *)
(* Lean:                                                                     *)
(*   Preservation/Complete/C701,C717,C973,C978,C979 (excludes_case =         *)
(*     CK_DirectPruning.excludes_case_of_remaining overlaps remaining, the   *)
(*     chains of Preservation/CK.lean),                                      *)
(*   Preservation/Complete/C713 + Cases/C713/Assembly                        *)
(*     (family_impossible_of_pair_stages, step 5 = C713ChordDirect.          *)
(*      source_to_after_height),                                             *)
(*   Cases/C898/CompleteCached + MixedCached (family_impossible,             *)
(*     mixed_impossible, fused chord 9-10),                                  *)
(*   Bridge/ChordPacking.transfer (chord stages bound to four owners),      *)
(*   Assembly/RowIdentity.family_at (the family is Phase-1 row ri).          *)
(*                                                                           *)
(* Everything here is bookkeeping in the owner vocabulary of                 *)
(* geometry/PackingContext.ml / CP_CommonCases_OriginalOwners.ml: under the row    *)
(* hypothesis  NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam  *)
(* every owner cover  oriented_pose_covered (MAP cr_leaf D) (owner m)  is    *)
(* derived from the initial covers (W-F6 CK_INITIAL via W-ENTRY's            *)
(* en_discharge) and the stage theorems (pair stages CK_STAGES / C8_STEPS,   *)
(* chords CK_CHORDS, C713_HEIGHT, C8_FUSED), whose square premises (unit     *)
(* normals, sides, lcont, pairwise ldisj, point facts) are discharged by     *)
(* W-ENTRY's en_case_bridge (= ChordPacking.transfer / owner_disjoint).      *)
(* The last stage of every chain has the empty target domain, which closes   *)
(* the case (Lean: List.not_mem_nil).                                        *)
(*                                                                           *)
(* Premises that other work packages still have to supply (W-F345 block     *)
(* overlaps, W-F6 initial covers) are kept as HYPOTHESES of the case theorem *)
(* (ASSUME of the exact statement-shape terms of §4.1/§4.3/§4.6), each with  *)
(* an OCaml name; once the real theorem is available, ca_provide registers   *)
(* it and ca_discharge removes the hypothesis (PROVE_HYP, or a conjunct-     *)
(* order-insensitive conversion for the initial covers).                     *)
(*                                                                           *)
(* OCaml API:                                                                *)
(*   ca_case c          : thm   H1, .., Hn |- EXCLUDED_ROW ri   (c = "701"..) *)
(*   ca_missing c       : (string * term) list  the hypotheses, named         *)
(*   ca_provide name th : register a theorem for a missing premise            *)
(*   ca_provide_initial (c, k) th, ca_provide_overlap (c, st) th              *)
(*   ca_discharge th    : remove every hypothesis of th that is provided      *)
(* Needs: EN_Entry.ml (Phase-1 chain), CR_HistStages + CK stage table,       *)
(* CH_Run (CK_CHORDS, C713_HEIGHT), C8_Run (C8_STEPS, C8_FUSED).            *)
(* ========================================================================= *)

needs "n12/cert/EN_Entry.ml";;

let ca_log s = Printf.printf "%s\n%!" s;;

(* ------------------------------------------------------------------------- *)
(* Data: domains, owners, chains.                                            *)
(* ------------------------------------------------------------------------- *)

let ca_dom_def c n = if c = "898" then c8dom_def n else hdom_def (c, n);;
let ca_dom_const c n = lhs (concl (ca_dom_def c n));;
let ca_owner_of_dom n = int_of_string (List.hd (String.split_on_char '_' n));;
let ca_mask c k =
  try let (m, _, _) = Hashtbl.find EN_OWNERS (c, k) in m
  with Not_found -> failwith (Printf.sprintf "ca_mask: no owner %d in C%s" k c);;
let ca_dom_mask c n = ca_mask c (ca_owner_of_dom n);;

(* the stages of a chain *)
type ca_stage =
    Spair of string * string * string * string            (* step, S, N, T *)
  | Schord of string * string * string list * string * int list   (* step, S, [N1;N2;N3], T, masks *)
  | Sheight                                                (* C713 step 5: 7_0 -> 7_6 *)
  | Sfused of string list;;                                (* C898 steps 9-10: S N1 N2 N3 M1 M2 M3 T *)

let ca_step_no s = match s with
    Spair (st, _, _, _) | Schord (st, _, _, _, _) -> int_of_string st
  | Sheight -> 5 | Sfused _ -> 9;;

let ca_chain c =
  let pairs = if c = "898" then map (fun (st, s, n, t, _) -> Spair (st, s, n, t)) c8_steps
    else map (fun (_, st, s, n, t, _) -> Spair (st, s, n, t))
           (filter (fun (c', _, _, _, _, _) -> c' = c) hist_stages) in
  let chords = map (fun (_, st, _, _, sd, td, ns, ms, _, _) -> Schord (st, sd, ns, td, ms))
                 (filter (fun (c', _, _, _, _, _, _, _, _, _) -> c' = c) ch_stages) in
  let extra = if c = "713" then [Sheight] else if c = "898" then [Sfused c8_fused_doms] else [] in
  List.sort (fun a b -> compare (ca_step_no a) (ca_step_no b)) (pairs @ chords @ extra);;

(* ------------------------------------------------------------------------- *)
(* Missing premises: names, statement terms, providers.                      *)
(* ------------------------------------------------------------------------- *)

let ca_pad2 st = if String.length st = 1 then "0" ^ st else st;;
let ca_overlap_name (c, st) = Printf.sprintf "C%s overlap S%s" c (ca_pad2 st);;
let ca_initial_name (c, k) = Printf.sprintf "C%s initial owner %d" c k;;

let CA_PROVIDED : (string, thm) Hashtbl.t = Hashtbl.create 300;;
let CA_TERMS : (string, term) Hashtbl.t = Hashtbl.create 300;;   (* name -> premise term *)

(* the pair-stage theorem (design §4.1 / §4.6) and its block-overlap premise *)
let ca_stage_thm c st = if c = "898" then c8_step_thm st else ck_stage_thm (c, st);;
let ca_overlap_term (c, st) = lhand (concl (ca_stage_thm c st));;

(* the CK_INITIAL.(k) term of design §4.3, exactly as W-F6's pv_owner_assemble
   states it (PV_OWNER_THM_D with the point lists expanded by the same rewrites):
     !c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
                 lcont c s u v a /\ linside c s u v a x1 y1 /\ .. /\ ~linside .. /\ ..
                 ==> oriented_pose_covered (MAP cr_leaf hC_dk_0) c s u v a
   points: n12/data/cert/pv_owners.txt / pv898_owners.txt (Lean insideK / outsideK) *)
let ca_rat_tm s = match String.split_on_char ':' s with
    [p; q] -> term_of_rat (Num.num_of_string p // Num.num_of_string q)
  | _ -> failwith ("ca_rat_tm " ^ s);;
let ca_pts_tm s =
  let pts = if s = "-" then [] else cr_split ';' s in
  mk_list (map (fun p -> match cr_split ',' p with
      [x; y] -> mk_pair (ca_rat_tm x, ca_rat_tm y)
    | _ -> failwith "ca_pts_tm") pts, `:real#real`);;
let CA_PV_OWNERS : (string * int, term * term) Hashtbl.t = Hashtbl.create 100;;
let () = List.iter (fun f -> List.iter (fun l -> match cr_split ' ' l with
      [c; k; _; ins; outs] -> Hashtbl.replace CA_PV_OWNERS (c, int_of_string k) (ca_pts_tm ins, ca_pts_tm outs)
    | _ -> ()) (cr_read_lines f)) ["n12/data/cert/pv_owners.txt"; "n12/data/cert/pv898_owners.txt"];;

let ca_initial_term (c, k) =
  let (ins, outs) = try Hashtbl.find CA_PV_OWNERS (c, k)
    with Not_found -> failwith (Printf.sprintf "ca_initial_term: no W-F6 owner record C%s %d" c k) in
  let d = ca_dom_const c (string_of_int k ^ "_0") in
  let tm = subst [ins, `ins:(real#real)list`; outs, `outs:(real#real)list`; d, `D:cpose list`]
   `forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
                lcont c s u v a /\
                (forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)) /\
                (forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P))
                ==> oriented_pose_covered (MAP cr_leaf D) c s u v a` in
  let pin = subst [ins, `ins:(real#real)list`]
              `forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)`
  and pout = subst [outs, `outs:(real#real)list`]
              `forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P)` in
  let mc = REWRITE_CONV[ALL_MEM; ALL; FST; SND] THENC REWRITE_CONV[] in
  let th = (PURE_REWRITE_CONV [mc pin; mc pout] THENC PURE_REWRITE_CONV [GSYM CONJ_ASSOC]) tm in
  rhs (concl th);;

let ca_provide name th =
  (try let t = Hashtbl.find CA_TERMS name in
       if hyp th <> [] then ca_log ("ca_provide: warning, " ^ name ^ " has hypotheses");
       ignore t
   with Not_found -> ());
  Hashtbl.replace CA_PROVIDED name th;;
let ca_provide_overlap key th = ca_provide (ca_overlap_name key) th;;
let ca_provide_initial key th = ca_provide (ca_initial_name key) th;;

(* prove the premise term t from a provided theorem th:
   either aconv, or (initial covers)  th : !c s u v a. A' ==> B,  t : !c s u v a. A ==> B
   with every conjunct of A' among the conjuncts of A (points compared as rationals) *)
let ca_conv_premise t th =
  if aconv (concl th) t then th else
  let (vs, body) = strip_forall t in
  let (a, b) = dest_imp body in
  let ha = CONJUNCTS (ASSUME a) in
  let th1 = SPECL vs th in
  let (a', b') = dest_imp (concl th1) in
  if not (aconv b b') then failwith "ca_conv_premise: conclusion" else
  let rat_eq x y = try rat_of_term x =/ rat_of_term y with Failure _ -> false in
  let rec same x y = aconv x y || (is_ratconst x && is_ratconst y && rat_eq x y) ||
    (is_comb x && is_comb y && same (rator x) (rator y) && same (rand x) (rand y)) in
  let one c' = try find (fun h -> aconv (concl h) c') ha with Failure _ ->
    let h = find (fun h -> same (concl h) c') ha in
    EQ_MP (EQT_ELIM ((REWRITE_CONV[] THENC REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[])
                       (mk_eq (concl h, c')))) h in
  let res = GENL vs (DISCH a (MP th1 (end_itlist CONJ (map one (conjuncts a'))))) in
  if aconv (concl res) t then res else failwith "ca_conv_premise";;

(* the theorem for a missing premise: provided, or assumed *)
let ca_premise name t =
  Hashtbl.replace CA_TERMS name t;
  try ca_conv_premise t (Hashtbl.find CA_PROVIDED name)
  with Not_found -> ASSUME t;;

(* remove every provided hypothesis *)
let ca_discharge th =
  Hashtbl.fold (fun name t th ->
      if not (exists (aconv t) (hyp th)) then th else
      try PROVE_HYP (ca_conv_premise t (Hashtbl.find CA_PROVIDED name)) th
      with Not_found -> th) CA_TERMS th;;

(* ------------------------------------------------------------------------- *)
(* Composition.                                                              *)
(* ------------------------------------------------------------------------- *)

(* cover theorems of a case: domain name -> |- !c1 c2 a b l. hyp ==> cov D (owner) *)
let CA_COVERS : (string * string, thm) Hashtbl.t = Hashtbl.create 300;;
let CA_USED : (string, (string * term) list) Hashtbl.t = Hashtbl.create 10;;

let ca_cov_concl c n =
  let m = ca_dom_mask c n in
  list_mk_comb (`oriented_pose_covered`,
    mk_comb (mk_comb (`MAP:(cpose->pose_leaf)->cpose list->pose_leaf list`, `cr_leaf`), ca_dom_const c n)
    :: en_owner m);;

let ca_check_cover c n th =
  let (_, fam) = en_family c in
  let want = mk_imp (en_hyp fam, ca_cov_concl c n) in
  if not (aconv (snd (strip_forall (concl th))) want) then
    failwith (Printf.sprintf "ca: cover of C%s %s has the wrong shape" c n)
  else th;;

let ca_note c name t =
  let l = try Hashtbl.find CA_USED c with Not_found -> [] in
  if not (exists (fun (n, _) -> n = name) l) then Hashtbl.replace CA_USED c (l @ [name, t]);;

let rec ca_cover c n =
  try Hashtbl.find CA_COVERS (c, n) with Not_found ->
  let parts = String.split_on_char '_' n in
  if List.nth parts 1 <> "0" then failwith (Printf.sprintf "ca: C%s domain %s not derived yet" c n) else
  (* initial cover of owner k (Lean CK_Entry.ownerK_cover = CertifiedOwner.sound) *)
  let k = ca_owner_of_dom n in
  let name = ca_initial_name (c, k) in
  let t = ca_initial_term (c, k) in
  ca_note c name t;
  let th = ca_check_cover c n (en_discharge (c, k) (ca_premise name t)) in
  Hashtbl.replace CA_COVERS (c, n) th; th;;

(* Lean ClosedInside facts of an owner, from its linside entry facts *)
let ca_closed_extra c m (x, y) =
  let tmpl = subst [x, `x:real`; y, `y:real`]
    `forall c s u v a. linside c s u v a x y ==> lclosed c s u v a x y` in
  let tmpl = prove (tmpl, REPEAT GEN_TAC THEN REWRITE_TAC[LINSIDE_CLOSED]) in
  en_case_bridge c [m] [] tmpl;;

let ca_run_stage c s =
  let t0 = Unix.gettimeofday () in
  let (tgt, th) = match s with
      Spair (st, sd, nd, td) ->
        let th0 = ca_stage_thm c st in
        let name = ca_overlap_name (c, st) in
        let ov = ca_overlap_term (c, st) in
        ca_note c name ov;
        let tr = MP th0 (ca_premise name ov) in
        let tmpl = PURE_REWRITE_RULE [cr_pair_transition] tr in
        (td, en_case_bridge c [ca_dom_mask c sd; ca_dom_mask c nd] [ca_cover c sd; ca_cover c nd] tmpl)
    | Schord (st, sd, ns, td, ms) ->
        let doms = sd :: ns in
        if map (ca_dom_mask c) doms <> ms then failwith ("ca: chord masks C" ^ c ^ " " ^ st) else
        let tmpl = PURE_REWRITE_RULE [ch_chord_transition] (ck_chord_thm (c, st)) in
        (td, en_case_bridge c ms (map (ca_cover c) doms) tmpl)
    | Sheight ->
        (* Lean C713ChordDirect.source_to_after_height: owner 2304 (owner 7) and the
           owners of masks 2, 512, 16384 holding the occupied-row points
           (1, 87/50), (2, 87/50), (3, 87/50) (C713OccupiedRow.above_radius) *)
        if ca_mask c 7 <> 2304 then failwith "ca: C713 owner 7" else
        ("7_6", en_case_bridge c [2304; 2; 512; 16384] [ca_cover c "7_0"] C713_HEIGHT)
    | Sfused doms ->
        (* Lean C898Chord.Fused.chord_fused, window ![4,0,6,10,3,5,8] of mixed_impossible
           = owners 5, 0, 7, 11, 3, 6, 9; cap and ClosedInside (q 4) (33/20, 33/20),
           (47/20, 33/20) from PointPremises.sound case898Domain5 (CompleteCached) *)
        let [sd; d1; d2; d3; e1; e2; e3; td] = doms in
        let srcs = [sd; d1; d2; d3; e1; e2; e3] in
        let ms = map (ca_dom_mask c) srcs in
        let m0 = hd ms in
        let closed = map (ca_closed_extra c m0) [(`&33 / &20`, `&33 / &20`); (`&47 / &20`, `&33 / &20`)] in
        let tmpl = PURE_REWRITE_RULE [c8_fused_transition] C8_FUSED in
        (td, en_case_bridge c ms (map (ca_cover c) srcs @ closed) tmpl) in
  let th = ca_check_cover c tgt th in
  Hashtbl.replace CA_COVERS (c, tgt) th;
  ca_log (Printf.sprintf "  C%s step %02d -> %s (%.1fs)" c (ca_step_no s) tgt (Unix.gettimeofday () -. t0));
  tgt;;

(* hyp |- F  ==>  |- EXCLUDED_ROW ri, keeping the other hypotheses (step6.excluded_of_false) *)
let ca_excluded ri h f =
  let th = GENL ROWVARS (NOT_INTRO (DISCH h f)) in
  EQ_MP (SYM (PURE_REWRITE_CONV [NOT_EXISTS_THM] (EXCLUDED_ROW ri))) th;;

let CA_CASES : (string, int * thm) Hashtbl.t = Hashtbl.create 10;;

let ca_case c =
  try snd (Hashtbl.find CA_CASES c) with Not_found ->
  let t0 = Unix.gettimeofday () in
  let (ri, fam) = en_family c in
  let chain = ca_chain c in
  let last = List.fold_left (fun _ s -> ca_run_stage c s) "" chain in
  (* the final domain is empty: oriented_pose_covered [] q <=> F *)
  let def = ca_dom_def c last in
  if rhs (concl def) <> mk_list ([], `:cpose`) then failwith ("ca: final domain not empty, C" ^ c) else
  let h = en_hyp fam in
  let cov = MP (SPECL EN_VARS (Hashtbl.find CA_COVERS (c, last))) (ASSUME h) in
  let f = CONV_RULE (PURE_REWRITE_CONV [def; MAP; oriented_pose_covered; MEM] THENC REWRITE_CONV []) cov in
  if concl f <> `false` then failwith ("ca: final cover did not reduce to F, C" ^ c) else
  let th = ca_excluded ri h f in
  Hashtbl.replace CA_CASES c (ri, th);
  ca_log (Printf.sprintf "C%s: |- EXCLUDED_ROW %d, %d stages, %d open hypotheses, %.1fs" c ri
            (length chain) (length (hyp th)) (Unix.gettimeofday () -. t0));
  th;;

(* the named hypotheses of the case theorem *)
let ca_missing c =
  let th = ca_case c in
  let used = try Hashtbl.find CA_USED c with Not_found -> [] in
  let l = filter (fun (_, t) -> exists (aconv t) (hyp th)) used in
  if length l <> length (hyp th) then failwith ("ca_missing: unnamed hypothesis in C" ^ c) else l;;

(* rebuild the case theorem without the provided hypotheses *)
let ca_close c =
  let (ri, th) = Hashtbl.find CA_CASES c in
  let th' = ca_discharge th in
  Hashtbl.replace CA_CASES c (ri, th'); th';;

let CA_CASE_IDS = ["701"; "713"; "717"; "973"; "978"; "979"; "898"];;
