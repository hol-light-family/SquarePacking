(* ========================================================================= *)
(* Port of Compact/Geometry/CentralRightChain.lean (Jatloe, N12-jatloe;      *)
(* namespace N12Compact.CentralRightChain).  The complete positive-frame     *)
(* B/R support selector is reduced to the genuine inward lower-U escape of   *)
(* R.  Normal is c977cc_normal; upper/lower are ABT_upper/ABT_lower;         *)
(* faceSeparation_of_disjoint + separated + radius identities:               *)
(* ABT_FOUR_AXES; CentralRightCornerSupport.lower_support /                  *)
(* negative_lower_support: CRCS_LOWER_SUPPORT / CRCS_NEGATIVE_LOWER_SUPPORT; *)
(* CentralRightMixedTransfer.steeper_wall_shift / shallower_reach /          *)
(* steeper_direction_reach: CRMT_STEEPER_WALL_SHIFT / CRMT_SHALLOWER_REACH / *)
(* CRMT_STEEPER_DIRECTION_REACH; PairedCornerPositiveWall.                   *)
(* negative_right_impossible: PCPW_NEGATIVE_RIGHT_IMPOSSIBLE.                *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CentralRightCornerSupport.ml";;
needs "n12/geometry/CentralRightMixedTransfer.ml";;
needs "n12/geometry/PairedCornerPositiveWall.ml";;

let CRCH_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CRCH_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

let CRCH_SB_TAC sq (x,y) (nx,ny) =
  MP_TAC(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)) THEN
  ANTS_TAC THENL [CRCH_ANTS_TAC; STRIP_TAC];;

let CRCH_QB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;
let CRCH_QR = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`];;

(* strict bounds of B at inner, low and of R at marker, high, in the four axes *)
let CRCH_BOUNDS_TAC =
  let inn = (`&113 / &50`,`&2`) and low = (`&3`,`&87 / &50`)
  and mk = (`&1543 / &500`,`&2`) and hi = (`&3`,`&12 / &5`) in
  let ds = [(`cB:real`,`sB:real`); (`--sB`,`cB:real`);
            (`cR:real`,`sR:real`); (`--sR`,`cR:real`)] in
  MAP_EVERY (fun d ->
    CRCH_SB_TAC CRCH_QB inn d THEN CRCH_SB_TAC CRCH_QB low d THEN
    CRCH_SB_TAC CRCH_QR mk d THEN CRCH_SB_TAC CRCH_QR hi d) ds THEN
  MP_TAC(SPECL CRCH_QB ABT_OWNU) THEN ANTS_TAC THENL [CRCH_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL CRCH_QR ABT_OWNU) THEN ANTS_TAC THENL [CRCH_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL CRCH_QR ABT_OWNV) THEN ANTS_TAC THENL [CRCH_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL (CRCH_QB @ CRCH_QR) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [CRCH_ANTS_TAC; DISCH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)));;

(* Lean: alternatives *)
let CRCH_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cR sR uR vR aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ c977cc_normal cR sR /\ aB = aR /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\ linside cB sB uB vB aB (&3) (&87 / &50) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> uB + aB <= ABT_lower cR sR uR vR aR cB sB \/
         ABT_upper cB sB uB vB aB cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CRCH_NORMAL_TAC THEN
  CRCH_BOUNDS_TAC THEN RASM_ARITH_TAC);;

(* Lean: lower_shift *)
let CRCH_LOWER_SHIFT = prove
 (`forall cB sB uB vB aB cR sR uR vR aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ c977cc_normal cR sR /\ aB = aR /\ &1 < aB /\
     lcont cR sR uR vR aR /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\ linside cB sB uB vB aB (&3) (&87 / &50) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cR sR uR vR aR (&3) (&3) /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\
     &2 * (cB + sB) <= uB
     ==> &3 * cR + &2 * sR < uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (CRCH_QB @ CRCH_QR) CRCH_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
  [MP_TAC(SPECL (CRCH_QR @ [`cB:real`; `sB:real`]) CRCS_LOWER_SUPPORT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cB * sR - sB * cR` THENL
  [MATCH_MP_TAC(SPECL (CRCH_QB @ CRCH_QR) CRMT_STEEPER_WALL_SHIFT) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(SPECL (CRCH_QB @ [`cR:real`; `sR:real`]) CRMT_SHALLOWER_REACH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (CRCH_QR @ [`cR:real`; `sR:real`]) CRCS_LOWER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL CRCH_QR ABT_OWNU) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_alternatives *)
let CRCH_NEGATIVE_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cR sR uR vR aR t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ c977cc_normal cR t /\ sR = --t /\ aB = aR /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\ linside cB sB uB vB aB (&3) (&87 / &50) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> uB + aB <= ABT_lower cR sR uR vR aR cB sB \/
         ABT_upper cB sB uB vB aB t cR <= vR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CRCH_NORMAL_TAC THEN
  SUBGOAL_THEN `ABT_upper cB sB uB vB aB (--sR) cR = ABT_upper cB sB uB vB aB t cR`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; ALL_TAC] THEN
  CRCH_BOUNDS_TAC THEN RASM_ARITH_TAC);;

(* Lean: negative_impossible *)
let CRCH_NEGATIVE_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cR sR uR vR aR cE sE uE vE aE t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\
     c977cc_normal cB sB /\ c977cc_normal cR t /\ sR = --t /\ &0 < t /\
     aB = aR /\ &1 < aB /\ lcont cR sR uR vR aR /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\ linside cB sB uB vB aB (&3) (&87 / &50) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\ linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&1543 / &500) (&3) /\
     linside cE sE uE vE aE (&3) (&1543 / &500) /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\ ldisj cE sE uE vE aE cR sR uR vR aR /\
     &2 * (cB + sB) <= uB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (CRCH_QB @ CRCH_QR @ [`t:real`]) CRCH_NEGATIVE_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
  [MP_TAC(SPECL (CRCH_QR @ [`cB:real`; `sB:real`; `t:real`]) CRCS_NEGATIVE_LOWER_SUPPORT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  CRCH_NORMAL_TAC THEN
  MP_TAC(SPECL [`cR:real`; `cB - sB`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`sB:real`; `cR - t`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= cB * cR - sB * t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL (CRCH_QB @ [`t:real`; `cR:real`]) CRMT_STEEPER_DIRECTION_REACH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC(SPECL (CRCH_QR @ [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`])
    PCPW_NEGATIVE_RIGHT_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;
