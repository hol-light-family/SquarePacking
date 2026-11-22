(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975TopOrigin.lean                *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* only").  The genuine merged-top origin (2,3) of owner 34816 in C975.      *)
(* owner p m is the 5-tuple (ooc .. m) .. l; a frame T is cT sT uT vT aT     *)
(* (its unit normal and positive side, implicit in Lean's OpenSquare, are    *)
(* explicit hypotheses).  The private closed is LINSIDE_CLOSED;              *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME; C849Negative.          *)
(* impossible: C849N_IMPOSSIBLE; fixed / northeast_selection / seed_point /  *)
(* aux_point / foreign: C975SS_ / C975SEL_ theorems, oo_seed, C975IC_ tools. *)
(* Tag C975TO_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975SelectionForward.ml";;
needs "n12/geometry/C849Negative.ml";;

(* Lean: negative_origin_exit *)
let C975TO_NEGATIVE_ORIGIN_EXIT = prove
 (`forall c s u v a. &0 < c /\ s <= &0 /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ linside c s u v a (&2) (&1543 / &500) /\
     ~linside c s u v a (&2) (&3)
     ==> ~linside c s u v a (&2) (&5 / &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C975TO_T = [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`];;
let C975TO_TIN = `forall x y. linside cT sT uT vT aT x y <=>
  linside (ooc c1 c2 a b l 34816) (oos c1 c2 a b l 34816) (oou c1 c2 a b l 34816) (oov c1 c2 a b l 34816) l x y`;;

(* Lean: negative_top_lower *)
let C975TO_NEGATIVE_TOP_LOWER = prove
 (list_mk_forall(C975IC_V5 @ C975TO_T,
   mk_imp(list_mk_conj [`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = c975d_family`;
                        `cT * cT + sT * sT = &1`; `&0 < aT`;
                        `&0 < cT`; `sT <= &0`; `--sT <= cT`; `(aT:real) = l`; C975TO_TIN],
          `linside cT sT uT vT aT (&2) (&5 / &2)`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aT:real = l`)) THEN
  ASM_CASES_TAC `linside cT sT uT vT l (&2) (&5 / &2)` THEN ASM_REWRITE_TAC[] THEN
  C975IC_COMPULSORY_TAC THEN
  MP_TAC (SPEC_ALL C975IC_TOP_LEFT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C975IP_POS 34816 `&33 / &20` `&47 / &20` [C975SS_NW_MARKER] THEN
  C975IP_POS 34816 `&8 / &5` `&3` [] THEN
  C975IP_POS 34816 `&2` `&1543 / &500` [C975SS_TOP_MARKER] THEN
  C975IP_NEG 34816 `&113 / &50` `&3` [1024, C975SEL_NORTHEAST_SELECTION] THEN
  C975IP_POS 4096 `&457 / &500` `&2` [C975IP_L_MARKER] THEN
  C975IP_POS 4096 `&1` `&12 / &5` [C975IP_L_HIGH] THEN
  C975IP_NEG 4096 `&19 / &25` `&187 / &100` [2, C975IP_L_SEED] THEN
  C975IP_NEG 4096 `&33 / &20` `&33 / &20` [256, C975SS_SW_MARKER] THEN
  C975IP_POS 192 `&1` `&1543 / &500` [C975IP_E_P] THEN
  C975IP_POS 192 `&457 / &500` `&3` [C975IP_E_Q] THEN
  C975IP_FRAME_TAC 4096 ["cL"; "sL"; "uL"; "vL"; "aL"] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = l`)) THEN
  MATCH_MP_TAC (SPECL ([`cT:real`; `sT:real`; `uT:real`; `vT:real`; `l:real`;
                        `cL:real`; `sL:real`; `uL:real`; `vL:real`; `l:real`] @ c975ic_owner 192)
                  C849N_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN
  FIRST [C975IP_SIDE_TAC [oo_apart C975D_F 34816 4096; oo_apart C975D_F 34816 192];
         ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINSIDE_CLOSED THEN ASM_REWRITE_TAC[] THEN NO_TAC]);;

(* Lean: top_origin *)
let C975TO_TOP_ORIGIN = prove
 (c975ic_stmt [] (c975ic_own 34816 `&2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975SS_NW_MARKER) THEN MP_TAC (SPEC_ALL C975SS_TOP_MARKER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C975IP_FRAME_TAC 34816 ["cT"; "sT"; "uT"; "vT"; "aT"] THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `linside`)) (concl th) &&
     is_iff (snd (strip_forall (concl th))) then ASSUME_TAC th THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  SUBGOAL_THEN `linside cT sT uT vT aT (&33 / &20) (&47 / &20) /\ linside cT sT uT vT aT (&2) (&1543 / &500)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sT` THENL
   [MAP_EVERY UNDISCH_TAC [`linside cT sT uT vT aT (&33 / &20) (&47 / &20)`;
                           `linside cT sT uT vT aT (&2) (&1543 / &500)`] THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `linside cT sT uT vT aT (&2) (&3)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL C975TO_T C975TO_NEGATIVE_ORIGIN_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC C975TO_NEGATIVE_TOP_LOWER THEN
  MAP_EVERY EXISTS_TAC C975IC_V5 THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;
