(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNonnegative.lean (Jatloe, N12-jatloe).    *)
(* The two genuine top omissions close the nonnegative merged-upper sector. *)
(* Lean structure Input A H is unfolded into explicit hypotheses (in field   *)
(* order, after the representation facts unit_normal / side_pos of A, H).   *)
(* Normal: c977cc_normal; lower / lower_in_bands: ABT_lower /                *)
(* C977NCO_LOWER_IN_BANDS; LowerNegative: C868LN_*; UpperGapScalars: C868GS_*.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/LowerNegative.ml";;
needs "n12/geometry/UpperGapScalars.ml";;

let C868UN_LIN_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* split every positive linside assumption into its four inequalities *)
let C868UN_EXPAND_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `linside`
    then STRIP_ASSUME_TAC(REWRITE_RULE[linside] th) else failwith "no"));;

let C868UN_BOUNDS_TAC =
  MAP_EVERY (fun tm ->
    let th = ASSUME tm in
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
  [`c977cc_normal cA (--sA)`; `c977cc_normal cH sH`];;

(* goal F from an assumption ~linside q x y *)
let C868UN_MISSING_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN C868UN_LIN_TAC;;

(* Lean: upper_faces *)
let C868UN_UPPER_FACES = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA (--sA) /\ c977cc_normal cH sH /\
     &1 < aA /\ aA = aH /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&2) (&2) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ~linside cH sH uH vH aH (&87 / &50) (&3) /\
     ~linside cH sH uH vH aH (&113 / &50) (&3) /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> &9 * cH < &35 * sH /\
         vH + aH <= &3 * cH - (&87 / &50) * sH /\
         (vH + aH <= &3 * cH - (&113 / &50) * sH \/
          uH + aH <= (&113 / &50) * cH + &3 * sH)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  C868UN_BOUNDS_TAC THEN
  SUBGOAL_THEN `(&87 / &50) * cH + &2 * sH <= uH` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPECL [`&87 / &50`; `&2`] o REWRITE_RULE[ldisj]) THEN
   C868UN_EXPAND_TAC THEN REWRITE_TAC[linside] THEN C868UN_LIN_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `vH + aH <= &3 * cH - (&87 / &50) * sH` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C868UN_EXPAND_TAC THEN
   C868UN_MISSING_TAC `~linside cH sH uH vH aH (&87 / &50) (&3)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [C868UN_EXPAND_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `vH + aH <= &3 * cH - (&113 / &50) * sH` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE] o
    check (fun th -> is_neg(concl th) && is_binary "real_le" (dest_neg(concl th)))) THEN
  C868UN_EXPAND_TAC THEN
  C868UN_MISSING_TAC `~linside cH sH uH vH aH (&113 / &50) (&3)`);;

(* Lean: impossible *)
let C868UN_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA (--sA) /\ c977cc_normal cH sH /\
     &1 < aA /\ aA = aH /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&2) (&2) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ~linside cH sH uH vH aH (&87 / &50) (&3) /\
     ~linside cH sH uH vH aH (&113 / &50) (&3) /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
    C868UN_UPPER_FACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
    C868LN_ONLY_LOWER_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    C868LN_MODES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  C868UN_BOUNDS_TAC THEN
  SUBGOAL_THEN `&9 * cH <= &35 * sH` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  (* the lower face of H in the direction (-sA, cA) *)
  SUBGOAL_THEN `&0 <= cH * cA - sH * --sA /\ &0 <= sH * cA + cH * --sA`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
   `vA + aH <= (sH * cA + cH * --sA) * uH + (cH * cA - sH * --sA) * vH`
  ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term ((=) `ABT_lower`)) (concl th))) THEN
   REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   SUBGOAL_THEN `abs(--sA * cH + cA * sH) = --sA * cH + cA * sH /\
                 abs(-- --sA * sH + cA * cH) = -- --sA * sH + cA * cH`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN CONJ_TAC THEN RASM_ARITH_TAC;
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `cA * (cH * cH + sH * sH) = cA /\ sA * (cH * cH + sH * sH) = sA`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  (* margins of UpperGapScalars, as needed *)
  let margin th = MP_TAC(SPECL [`cH:real`; `sH:real`; `cA:real`; `--sA`] th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] in
  let topcases = FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `&113 / &50`)) (concl th))) in
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `&8 / &5`)) (concl th))) THENL
  [(* (8/5)C - s <= loV: v > 0 against U, V < 0 *)
   C868UN_EXPAND_TAC THEN
   C868LN_PROD `&0 <= (sH * cA + cH * --sA) * (&2 * (cH + sH) - uH)` THEN
   C868LN_PROD `&0 <= (cH * cA - sH * --sA) * (&2 * (cH - sH) - vH)` THEN
   NLIN_TAC ~deg2:false [];
   (* shallow lower square *)
   margin C868GS_THIRD THEN margin C868GS_FOURTH THEN
   C868UN_EXPAND_TAC THEN topcases THENL
   [C868LN_PROD `&0 <= (sH * cA + cH * --sA) *
       ((--(&7 / &20) * cH + (&7 / &20) * sH) - (uH - &2 * (cH + sH)))` THEN
    C868LN_PROD `&0 <= (cH * cA - sH * --sA) *
       (cH - (&13 / &50) * sH - aH - (vH - &2 * (cH - sH)))` THEN
    C868LN_PROD `&0 <= (aH - &1) * (cH * cA - sH * --sA)` THEN
    NLIN_TAC ~deg2:false [];
    C868LN_PROD `&0 <= (sH * cA + cH * --sA) *
       ((&13 / &50) * cH + sH - aH - (uH - &2 * (cH + sH)))` THEN
    C868LN_PROD `&0 <= (cH * cA - sH * --sA) *
       (cH + (&13 / &50) * sH - aH - (vH - &2 * (cH - sH)))` THEN
    C868LN_PROD `&0 <= (aH - &1) * ((cH * cA - sH * --sA) + (sH * cA + cH * --sA))` THEN
    NLIN_TAC ~deg2:false []];
   (* third mode *)
   margin C868GS_FIRST THEN margin C868GS_SECOND THEN
   C868UN_EXPAND_TAC THEN topcases THENL
   [C868LN_PROD `&0 <= (sH * cA + cH * --sA) *
       ((--(&7 / &20) * cH + (&7 / &20) * sH) - (uH - &2 * (cH + sH)))` THEN
    C868LN_PROD `&0 <= (cH * cA - sH * --sA) *
       (cH - (&13 / &50) * sH - aH - (vH - &2 * (cH - sH)))` THEN
    C868LN_PROD `&0 < (aH - &1) * (&1 + (cH * cA - sH * --sA))` THEN
    NLIN_TAC ~deg2:false [];
    C868LN_PROD `&0 <= (sH * cA + cH * --sA) *
       ((&13 / &50) * cH + sH - aH - (uH - &2 * (cH + sH)))` THEN
    C868LN_PROD `&0 <= (cH * cA - sH * --sA) *
       (cH + (&13 / &50) * sH - aH - (vH - &2 * (cH - sH)))` THEN
    C868LN_PROD `&0 < (aH - &1) *
       (&1 + (cH * cA - sH * --sA) + (sH * cA + cH * --sA))` THEN
    NLIN_TAC ~deg2:false []]]);;
