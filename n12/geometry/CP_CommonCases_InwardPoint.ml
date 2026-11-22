(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/InwardPoint.lean                   *)
(* (N12Compact.CommonCases.InwardPoint).  The inward central square owns a   *)
(* strict horizontal bar for every orientation.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let CCIP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let CCIP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_strong (private) *)
let CCIP_POSITIVE_STRONG = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&0) (&0) /\
      linside c s u v a (&7 / &20) (--(&9 / &100)) /\
      linside c s u v a (&13 / &50) (&13 / &50) /\
      ~linside c s u v a (--(&7 / &20)) (--(&9 / &100)) /\
      ~linside c s u v a (&2 / &5) (--(&37 / &50))
      ==> linside c s u v a (&27 / &50) (&1 / &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&89 / &100` `&17 / &50`) THEN
  MP_TAC(WFP_SP `&7 / &50` `&99 / &100`) THEN
  MP_TAC(WFP_SP `--(&3 / &4)` `&13 / &20`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&61 * s <= &35 * c` THEN CCIP_LIN_TAC);;

(* Lean: negative_strong (private) *)
let CCIP_NEGATIVE_STRONG = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
      linside c s u v a (&0) (&0) /\
      linside c s u v a (&7 / &20) (--(&9 / &100)) /\
      linside c s u v a (&13 / &50) (&13 / &50) /\
      ~linside c s u v a (--(&7 / &20)) (--(&9 / &100)) /\
      ~linside c s u v a (&7 / &20) (&61 / &100) /\
      ~linside c s u v a (&2 / &5) (--(&37 / &50))
      ==> linside c s u v a (&27 / &50) (&1 / &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&89 / &100` `&17 / &50`) THEN
  MP_TAC(WFP_SP `&7 / &50` `&99 / &100`) THEN
  MP_TAC(WFP_SP `&3 / &4` `--(&13 / &20)`) THEN
  MP_TAC(WFP_SP `&7 / &10` `&7 / &10`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&19 * c <= &34 * t` THEN CCIP_LIN_TAC);;

(* Lean: strong *)
let CCIP_STRONG = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&0) (&0) /\
      linside c s u v a (&7 / &20) (--(&9 / &100)) /\
      linside c s u v a (&13 / &50) (&13 / &50) /\
      ~linside c s u v a (--(&7 / &20)) (--(&9 / &100)) /\
      ~linside c s u v a (&7 / &20) (&61 / &100) /\
      ~linside c s u v a (&2 / &5) (--(&37 / &50))
      ==> linside c s u v a (&27 / &50) (&1 / &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC CCIP_POSITIVE_STRONG THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CCIP_NEGATIVE_STRONG THEN EXISTS_TAC `--s1` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: strong_original *)
let CCIP_STRONG_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&2) (&87 / &50) /\
      linside c s u v a (&113 / &50) (&2) /\
      ~linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&12 / &5) (&1)
      ==> linside c s u v a (&127 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &87 / &50)`;
                `v - (--s * &2 + c * &87 / &50)`; `a:real`] CCIP_STRONG) THEN
  REWRITE_TAC[CCIP_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: point_original (the triangle certificate is replaced by the       *)
(* explicit convex combination 272/971, 8/971, 691/971 of the three        *)
(* strictly owned points)                                                   *)
let CCIP_POINT_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&2) (&87 / &50) /\
      linside c s u v a (&113 / &50) (&2) /\
      ~linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&12 / &5) (&1)
      ==> linside c s u v a (&123 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    CCIP_STRONG_ORIGINAL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a (&113 / &50) (&2)` THEN
  UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
