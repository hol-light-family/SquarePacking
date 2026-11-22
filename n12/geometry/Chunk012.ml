(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Data/Prefix10Chunks/Chunk012.lean    *)
(* (S12Completion.C981.Coverage.prefix10Chunk012): a literal table of C981 coverage *)
(* fronts (71 rows).  Entries are the FinsetPool constants c981fp_fsNN.   *)
(* HOL file name follows n12/scripts/ready.py hname (unique short name).        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FinsetPool.ml";;

(* Lean: prefix10Chunk012 *)
let c981cov_prefix10chunk012 = new_definition
 `c981cov_prefix10chunk012 : ((num->bool)list)list = [
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs13];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs19];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs10; c981fp_fs49; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs13];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs19];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs15];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs20];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs16];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs13];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs19];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs15];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs20];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs16];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs15];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs20];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs15];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs20];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs13];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs19];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs13];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs19];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs12];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs34; c981fp_fs45; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs18];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs37];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs16];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs39];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs29; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs22; c981fp_fs29; c981fp_fs00; c981fp_fs00; c981fp_fs16];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs37];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs16];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs39];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs29; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs26; c981fp_fs29; c981fp_fs00; c981fp_fs00; c981fp_fs16];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs37];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs23; c981fp_fs29; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs37];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs43; c981fp_fs28; c981fp_fs29; c981fp_fs00; c981fp_fs00; c981fp_fs14];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs46; c981fp_fs22; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs46; c981fp_fs26; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs46; c981fp_fs23; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31];
   [c981fp_fs06; c981fp_fs03; c981fp_fs05; c981fp_fs11; c981fp_fs46; c981fp_fs28; c981fp_fs00; c981fp_fs00; c981fp_fs00; c981fp_fs31]]`;;
