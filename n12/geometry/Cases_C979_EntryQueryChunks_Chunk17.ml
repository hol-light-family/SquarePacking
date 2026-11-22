(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk17.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC17_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Chunk49.ml";;
needs "n12/geometry/Queries028.ml";;
needs "n12/geometry/Queries029.ml";;
needs "n12/geometry/Queries030.ml";;
needs "n12/geometry/Queries031.ml";;

(* Lean: single979_8_1 *)
let c979eqc17_single979_8_1 = { dmask = 4096; dlower = 1; dupper = 3;
  dallowed = [[0]; [1]; [0; 1]; [3]; [0; 3]; [1; 3]; [0; 1; 3]];
  dqueries = [1039; 1040; 1041; slq_hist_idx 900; 1042; slq_hist_idx 901; slq_hist_idx 902; 1043; 1044; 1045; slq_hist_idx 903; 1046; slq_hist_idx 904; slq_hist_idx 905; 1047; slq_hist_idx 906; slq_hist_idx 907; slq_hist_idx 908; 1048; 1049; 1050; slq_hist_idx 909; 1051; slq_hist_idx 910; slq_hist_idx 911; 1052; slq_hist_idx 912; slq_hist_idx 913; slq_hist_idx 914; 1053; slq_hist_idx 915; slq_hist_idx 916; slq_hist_idx 917; slq_hist_idx 918; 1054; 1055; 1056; slq_hist_idx 919; 1057; slq_hist_idx 920; slq_hist_idx 921; 1058; slq_hist_idx 922; slq_hist_idx 923; slq_hist_idx 924; 1059; slq_hist_idx 925; slq_hist_idx 926; slq_hist_idx 927; slq_hist_idx 928; 1060; slq_hist_idx 929; slq_hist_idx 930; slq_hist_idx 931; slq_hist_idx 932; slq_hist_idx 933; 1061; 1062; 1063; slq_hist_idx 934; 1064; slq_hist_idx 935; slq_hist_idx 936; 1065; slq_hist_idx 937; slq_hist_idx 938; slq_hist_idx 939; 1066; slq_hist_idx 940; slq_hist_idx 941; slq_hist_idx 942; slq_hist_idx 943; 1067; slq_hist_idx 944; slq_hist_idx 945; slq_hist_idx 946; slq_hist_idx 947; slq_hist_idx 948; 1068; slq_hist_idx 949; slq_hist_idx 950; slq_hist_idx 951; slq_hist_idx 952; slq_hist_idx 953; slq_hist_idx 954; 1069; 1070; 1071; slq_hist_idx 955; 1072; slq_hist_idx 956; slq_hist_idx 957; 1073; slq_hist_idx 958; slq_hist_idx 959; slq_hist_idx 960; 1074; slq_hist_idx 961; slq_hist_idx 962; slq_hist_idx 963; slq_hist_idx 964; 1075; slq_hist_idx 965; slq_hist_idx 966; slq_hist_idx 967; slq_hist_idx 968; slq_hist_idx 969; 1076; slq_hist_idx 970; slq_hist_idx 971; slq_hist_idx 972; slq_hist_idx 973; slq_hist_idx 974; slq_hist_idx 975; 1077; slq_hist_idx 976; slq_hist_idx 977; slq_hist_idx 978; slq_hist_idx 979; slq_hist_idx 980; slq_hist_idx 981; slq_hist_idx 982; 1078; 1079; 1080; slq_hist_idx 983; 1081; slq_hist_idx 984; slq_hist_idx 985; 1082; slq_hist_idx 986; slq_hist_idx 987; slq_hist_idx 988; 1083; slq_hist_idx 989; slq_hist_idx 990; slq_hist_idx 991; slq_hist_idx 992; 1084; slq_hist_idx 993; slq_hist_idx 994; slq_hist_idx 995; slq_hist_idx 996; slq_hist_idx 997; 1085; slq_hist_idx 998; slq_hist_idx 999; slq_hist_idx 1000; slq_hist_idx 1001; slq_hist_idx 1002; slq_hist_idx 1003; 1086; slq_hist_idx 1004; slq_hist_idx 1005; slq_hist_idx 1006; slq_hist_idx 1007; slq_hist_idx 1008; slq_hist_idx 1009; slq_hist_idx 1010; 1087; slq_hist_idx 1011; slq_hist_idx 1012; slq_hist_idx 1013; slq_hist_idx 1014; slq_hist_idx 1015; slq_hist_idx 1016; slq_hist_idx 1017; slq_hist_idx 1018] };;
(* Lean: single979_8_1_checked *)
let C979EQC17_SINGLE979_8_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc17_single979_8_1;;
