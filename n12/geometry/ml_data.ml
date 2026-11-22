(* MergedLower / Endpoint684 domain data: n12/scripts/ml_extract.py *)
let qn = nlin_rat;;
let ML_CASES = [
  (71, [1; 2; 4; 8; 48; 192; 768; 1024; 2048; 4096; 16384; 32768], [(1, Xrcomb 1); (2, Xrcomb 3); (4, Xrtr(1,(false,true,false))); (8, Xrtr(3,(false,true,false))); (4096, Xrcomb 17); (16384, Xrcomb 21); (32768, Xrcomb 24); (1024, Xrtr(13,(false,true,false))); (2048, Xrcomb 13)]);
  (80, [1; 2; 4; 8; 48; 192; 1024; 2048; 4096; 8960; 16384; 32768], [(1, Xrcomb 1); (2, Xrcomb 3); (4, Xrtr(1,(false,true,false))); (8, Xrtr(3,(false,true,false))); (4096, Xrcomb 17); (16384, Xrcomb 21); (32768, Xrcomb 24); (1024, Xrtr(13,(false,true,false))); (2048, Xrcomb 13)]);
  (589, [1; 2; 8; 48; 192; 768; 1024; 2048; 4096; 8192; 16384; 32768], [(1, Xrcomb 1); (2, Xrcomb 3); (8, Xrtr(3,(false,true,false))); (4096, Xrcomb 17); (8192, Xrcomb 19); (16384, Xrcomb 21); (32768, Xrcomb 24); (1024, Xrtr(13,(false,true,false))); (2048, Xrcomb 13)]);
  (590, [1; 2; 8; 48; 192; 768; 1024; 2048; 4096; 8196; 16384; 32768], [(1, Xrcomb 1); (2, Xrcomb 3); (8, Xrtr(3,(false,true,false))); (4096, Xrcomb 17); (8196, Xpprod(Prspec(70,0),Prsmall(1,5,([(qn"9/4",qn"1"); (qn"11/4",qn"1"); (qn"9/4",qn"1")],(qn"113/50",qn"1"),qn"1/50",qn"0")))); (16384, Xrcomb 21); (32768, Xrcomb 24); (1024, Xrtr(13,(false,true,false))); (2048, Xrcomb 13)]);
  (684, [1; 2; 12; 16; 32; 192; 256; 512; 3072; 4096; 16384; 32768], [(1, Xrcomb 1); (2, Xrcomb 3); (16, Xrtr(1,(false,true,true))); (32, Xrtr(3,(false,true,true))); (4096, Xrcomb 17); (16384, Xrcomb 21); (32768, Xrcomb 24); (256, Xrcomb 6); (512, Xrcomb 8)]);
];;
