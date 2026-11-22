(* ========================================================================= *)
(* Whole-case geometric arguments of Jatloe's MergedTopFurther/Complete and  *)
(* C849851/{Positive,Complete}, stated over the original squares (no frame) *)
(* so that the case engine (bridge_ext.ml, apply_tmpl) discharges every      *)
(* premise from the packing.  The canonical / positive frame changes        *)
(* (ClosedFrames) are done inside the proofs, exactly as in Lean.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/MergedTopFurtherGeometry.ml";;
needs "n12/geometry/C849Negative.ml";;
needs "n12/geometry/FourSquareANarrow.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;

(* introduce a frame of square (c s u v a) with the given names *)
let FRAME_TAC lemma (c, s, u, v, a) names =
  let [c'; s'; u'; v'; a'] = map (fun n -> mk_var(n, `:real`)) names in
  MP_TAC(SPECL [c; s; u; v; a] lemma) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN c' (X_CHOOSE_THEN s' (X_CHOOSE_THEN u' (X_CHOOSE_THEN v'
    (X_CHOOSE_THEN a' STRIP_ASSUME_TAC)))));;

(* prove the premises of a lemma from the (expanded) assumptions; the frame
   equivalences (!x y. linside X' x y <=> linside X x y) translate the goals *)
let frame_eqs (asl, _) =
  filter (fun th -> let t = snd (strip_forall (concl th)) in is_iff t &&
            (let h = fst(strip_comb(lhand t)) in h = `linside` || h = `lclosed`)) (map snd asl);;
let PREMS_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> (REWRITE_TAC([ldisj; lcont] @ frame_eqs g) THEN FIRST_ASSUM ACCEPT_TAC) g) ORELSE
   ASM_REAL_ARITH_TAC);;
let USE_TAC th = MP_TAC th THEN ANTS_TAC THENL [PREMS_TAC; ALL_TAC];;

let A5 = (`cA:real`, `sA:real`, `uA:real`, `vA:real`, `aA:real`);;
let sqv (c, s, u, v, a) = [c; s; u; v; a];;
let sqn p = let f x = mk_var(x ^ p, `:real`) in (f "c", f "s", f "u", f "v", f "a");;

(* Lean: MergedTopFurther.impossible  (A = owner 5, B = owner 9, R = owner 3,
   C = owner 2, E = the 192 owner, L = owner 6) *)
let MTF_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR cC sC uC vC aC cE sE uE vE aE cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\ lsquare cR sR uR vR aR /\
     lsquare cC sC uC vC aC /\ lsquare cE sE uE vE aE /\ lsquare cL sL uL vL aL /\
     &1 < aA /\ aA <= &1001 / &1000 /\ aA = aB /\ aB = aR /\ aB = aC /\ aB = aE /\ aB = aL /\
     lcont cE sE uE vE aE /\ lcont cL sL uL vL aL /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\ lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\ linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\ ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\ linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\ linside cB sB uB vB aB (&2) (&1543 / &500) /\
     linside cR sR uR vR aR (&3) (&113 / &50) /\ linside cR sR uR vR aR (&3) (&72 / &25) /\
     linside cC sC uC vC aC (&113 / &50) (&3) /\
     linside cE sE uE vE aE (&1) (&3) /\ linside cE sE uE vE aE (&1) (&1543 / &500) /\
     linside cE sE uE vE aE (&457 / &500) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\ lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\ ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\ ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cC sC uC vC aC /\ ldisj cB sB uB vB aB cE sE uE vE aE /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  USE_TAC(SPECL (sqv A5 @ sqv (sqn "B") @ sqv (sqn "R")) MTFG_A_HIGH) THEN DISCH_TAC THEN
  MP_TAC(SPECL (sqv (sqn "R")) MTFG_RIGHT_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&12 / &5)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aR` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&3`; `&12 / &5`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&2) (&5 / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&5 / &2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&113 / &50) (&3)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cB sB uB vB aB cC sC uC vC aC` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&113 / &50`; `&3`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  FRAME_TAC CLF_CANONICAL_FRAME (sqn "B") ["cb"; "sb"; "ub"; "vb"; "ab"] THEN
  ASM_CASES_TAC `&0 <= sb` THENL
   [USE_TAC(SPECL (sqv A5 @ [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`] @
                   sqv (sqn "C") @ sqv (sqn "E")) MTFG_POSITIVE_IMPOSSIBLE) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FRAME_TAC CLF_CANONICAL_FRAME (sqn "L") ["cl"; "sl"; "ul"; "vl"; "al"] THEN
  USE_TAC(SPECL ([`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `al:real`] @ sqv (sqn "E")) C849N_IMPOSSIBLE) THEN
  REWRITE_TAC[]);;

(* Lean: C849851.impossible (+ Positive.negative_frame, a_high, positive_impossible);
   A = owner 7 (1024), R = owner 8 (right), B = owner 9 (34816), C = owner 2 (16),
   E = the 192 owner, L = owner 3 (4096) *)
let C849851_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cB sB uB vB aB cC sC uC vC aC cE sE uE vE aE cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\ lsquare cR sR uR vR aR /\
     lsquare cC sC uC vC aC /\ lsquare cE sE uE vE aE /\ lsquare cL sL uL vL aL /\
     &1 < aA /\ aA <= &1001 / &1000 /\ aA = aB /\ aB = aR /\ aB = aC /\ aB = aE /\ aB = aL /\
     lcont cR sR uR vR aR /\ lcont cE sE uE vE aE /\ lcont cL sL uL vL aL /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\ lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\ linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\ ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\ ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\ lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cR sR uR vR aR (&3) (&87 / &50) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\ linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\ linside cB sB uB vB aB (&2) (&1543 / &500) /\
     linside cC sC uC vC aC (&113 / &50) (&3) /\
     linside cE sE uE vE aE (&1) (&3) /\ linside cE sE uE vE aE (&1) (&1543 / &500) /\
     linside cE sE uE vE aE (&457 / &500) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\ lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\ ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\ ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cB sB uB vB aB cC sC uC vC aC /\ ldisj cB sB uB vB aB cE sE uE vE aE /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ldisj cR sR uR vR aR cA sA uA vA aA` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aR` THEN REWRITE_TAC[ldisj] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_TAC(SPECL (sqv (sqn "R") @ sqv A5) FSLB_RIGHT_POINT) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&5 / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aR` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&3`; `&5 / &2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (&2) (&5 / &2)` ASSUME_TAC THENL
   [FRAME_TAC CLF_POSITIVE_FRAME A5 ["ca"; "sa"; "ua"; "va"; "aa"] THEN
    FIRST_ASSUM(fun th -> if is_forall (concl th) && fst(strip_comb(lhand(snd(strip_forall(concl th))))) = `linside`
                          then ONCE_REWRITE_TAC[GSYM th] else NO_TAC) THEN
    USE_TAC(SPECL [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aa:real`] FSAN_POINT_OF_HIGHER_R) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&2) (&5 / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&5 / &2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&113 / &50) (&3)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cB sB uB vB aB cC sC uC vC aC` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&113 / &50`; `&3`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  FRAME_TAC CLF_CANONICAL_FRAME (sqn "B") ["cb"; "sb"; "ub"; "vb"; "ab"] THEN
  ASM_CASES_TAC `&0 <= sb` THENL
   [USE_TAC(SPECL (sqv A5 @ [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`] @
                   sqv (sqn "C") @ sqv (sqn "E")) MTFG_POSITIVE_IMPOSSIBLE) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FRAME_TAC CLF_CANONICAL_FRAME (sqn "L") ["cl"; "sl"; "ul"; "vl"; "al"] THEN
  USE_TAC(SPECL ([`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `al:real`] @ sqv (sqn "E")) C849N_IMPOSSIBLE) THEN
  REWRITE_TAC[]);;
