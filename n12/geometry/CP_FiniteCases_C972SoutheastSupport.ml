(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SoutheastSupport.lean          *)
(* (namespace N12Compact.FiniteCases.C972).  Strict points and actual        *)
(* southwest faces in C972's remaining SE branch.  owners p i = owner of     *)
(* mask EL i c972o_masks, written with the literal mask (owners 0..11 =      *)
(* masks 1,2,12,48,192,256,512,1024,2048,4096,8192,16384).  fixed =          *)
(* C972CS_FIXED (C972CS_FIXED_TAC), foreign / apart = C972CS_CLASH_TAC.      *)
(* pullX / pullSwap tuples as in C972UpperReduction (c972ur_px, c983ld_sw);  *)
(* q.translated 2 2 as in C972NorthwestForward (C972NF_TRANSLATED).          *)
(* C1090.ResidualCentralPoints.mixed_point = C1090RCP_MIXED_POINT,           *)
(* InwardPoint.strong_original = CCIP_STRONG_ORIGINAL.                       *)
(* The OpenSquare C of the face lemmas is cC sC uC vC aC (its unit normal    *)
(* and positive side are not needed and not assumed); the hypothesis actual  *)
(* is  !x y. linside cC sC uC vC aC x y <=> linside (owners p 5) (2+x) (2+y).*)
(* Tag C972SS_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972SoutheastReduction.ml";;
needs "n12/geometry/CP_FiniteCases_C972NorthwestForward.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualCentralPoints.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;

let c972ss_own = c972mc_own and c972ss_stmt = c972mc_stmt and c972ss_tuple = c972mc_tuple;;

(* q.translated 2 2 of a 5-tuple *)
let c972ss_tr22 t = match t with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`])
                         [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`; `a:real`]
  | _ -> failwith "c972ss_tr22";;

(* Lean: northwest_mixed_point *)
let C972SS_NORTHWEST_MIXED_POINT = prove
 (c972ss_stmt [c972ss_own 1024 `&2` `&3`] (c972ss_own 2048 `&79 / &50` `&54 / &25`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972NF_NORTHWEST_FORWARD) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C972CS_OWNER_TAC 2048 THEN
  MP_TAC(SPECL (c972ss_tr22 (c972ur_px (c972ss_tuple 2048))) C1090RCP_MIXED_POINT) THEN
  REWRITE_TAC[C972NF_TRANSLATED] THEN REWRITE_TAC[LINSIDE_PULLX] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC);;

(* Lean: southwest_strong_tips *)
let C972SS_SOUTHWEST_STRONG_TIPS = prove
 (c972ss_stmt [] (mk_conj(c972ss_own 256 `&73 / &50` `&199 / &100`,
                          c972ss_own 256 `&199 / &100` `&73 / &50`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 256 THEN
  C972CS_SH `&8 / &5` THEN C972CS_SV `&8 / &5` THEN CONJ_TAC THENL
   [MP_TAC(SPECL (c972ur_px (c972ss_tuple 256)) CCIP_STRONG_ORIGINAL) THEN
    REWRITE_TAC[LINSIDE_PULLX] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC;
    MP_TAC(SPECL (c972ur_px (c983ld_sw (c972ss_tuple 256))) CCIP_STRONG_ORIGINAL) THEN
    REWRITE_TAC[LINSIDE_PULLX] THEN REWRITE_TAC[LINSIDE_PULLSW] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC]);;

(* Lean: positive_cap (private) *)
let C972SS_POSITIVE_CAP = prove
 (`forall c s u v a. &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (--(&1 / &2)) (&0) /\ linside c s u v a (--(&13 / &50)) (&0) /\
     ~linside c s u v a (--(&21 / &50)) (&4 / &25)
     ==> v + a <= &21 / &50 * s + &4 / &25 * c`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: negative_faces (private) *)
let C972SS_NEGATIVE_FACES = prove
 (`forall c s u v a. &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (--(&13 / &50)) (&0) /\ linside c s u v a (--(&27 / &50)) (--(&1 / &100)) /\
     ~linside c s u v a (--(&21 / &50)) (&4 / &25)
     ==> (--(&21 / &50) * c + &4 / &25 * s <= u /\ &12 * c < -- &17 * s) \/
         v + a <= &21 / &50 * s + &4 / &25 * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  ASM_CASES_TAC `--(&21 / &50) * c + &4 / &25 * s <= u` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* the upper-u face of southwest_positive_faces (its le_of_not_gt step) *)
let C972SS_POSITIVE_FACE = prove
 (`forall c s u v a. &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&0) (--(&13 / &50)) /\ linside c s u v a (--(&13 / &50)) (&0) /\
     ~linside c s u v a (&13 / &50) (&0)
     ==> u + a <= &13 / &50 * c`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C972SS_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let c972ss_actual =
  let lc = list_mk_comb(`linside`, C972SS_C @ [`x:real`; `y:real`]) in
  let ro = list_mk_comb(`linside`, c972ss_tuple 256 @ [`&2 + x`; `&2 + y`]) in
  list_mk_forall([`x:real`; `y:real`], mk_eq(lc, ro));;
let c972ss_face_stmt hyps body =
  list_mk_forall(C972MC_V5 @ C972SS_C,
    mk_imp(list_mk_conj([C972MC_NP; C972MC_IMG; mk_neg (c972ss_own 512 `&3` `&3 / &2`); c972ss_actual] @ hyps),
           body));;
let C972SS_CAP_TM = `vC + aC <= &21 / &50 * sC + &4 / &25 * cC`;;

(* the facts used by the three face theorems *)
let C972SS_FACTS_TAC =
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_WEST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972SS_SOUTHWEST_STRONG_TIPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972SR_SOUTHEAST_G6_OF_MISSING_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972SR_NORTHEAST_ORIGIN_OF_MISSING_SOUTHEAST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972SS_NORTHWEST_MIXED_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC;;

let C972SS_CLOSE_TAC =
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C972CS_CLASH_TAC;;

(* Lean: southwest_positive_cap *)
let C972SS_SOUTHWEST_POSITIVE_CAP = prove
 (c972ss_face_stmt [`&0 < cC`; `&0 <= sC`; `sC <= cC`] C972SS_CAP_TM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972SS_FACTS_TAC THEN
  MATCH_MP_TAC (SPECL C972SS_C C972SS_POSITIVE_CAP) THEN C972SS_CLOSE_TAC);;

(* Lean: southwest_positive_faces *)
let C972SS_SOUTHWEST_POSITIVE_FACES = prove
 (c972ss_face_stmt [`&0 < cC`; `&0 <= sC`; `sC <= cC`]
    (mk_conj(`uC + aC <= &13 / &50 * cC`, C972SS_CAP_TM)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972SS_FACTS_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC (SPECL C972SS_C C972SS_POSITIVE_FACE); MATCH_MP_TAC (SPECL C972SS_C C972SS_POSITIVE_CAP)] THEN
  C972SS_CLOSE_TAC);;

(* Lean: southwest_negative_faces *)
let C972SS_SOUTHWEST_NEGATIVE_FACES = prove
 (c972ss_face_stmt [`&0 < cC`; `sC <= &0`; `--sC <= cC`]
    (mk_disj(`--(&21 / &50) * cC + &4 / &25 * sC <= uC /\ &12 * cC < -- &17 * sC`, C972SS_CAP_TM)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972SS_FACTS_TAC THEN
  MATCH_MP_TAC (SPECL C972SS_C C972SS_NEGATIVE_FACES) THEN C972SS_CLOSE_TAC);;
