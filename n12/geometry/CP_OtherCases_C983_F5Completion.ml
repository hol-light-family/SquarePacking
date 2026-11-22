(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F5Completion.lean              *)
(* (N12Compact.Completion.OtherCases.C983).  The F5 branch of case C983:     *)
(* f5_pairwise_three_square_entrance                                        *)
(* (C983F5TSE_F5_PAIRWISE_THREE_SQUARE_ENTRANCE) and the shared ending       *)
(* NegativeTripleEnd.impossible (C983NTE_IMPOSSIBLE).  Tag C983F5CO_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5ThreeSquareEntrance.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeTripleEnd.ml";;

(* Lean: f5_impossible *)
let C983F5CO_F5_IMPOSSIBLE = prove
 (c983sa_stmt [c983f4f_mem 5 7] `false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C983F5TSE_F5_PAIRWISE_THREE_SQUARE_ENTRANCE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; c983f5tse_tripleinput] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C983NTE_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                        `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
  ASM_REWRITE_TAC[ldisj]);;
