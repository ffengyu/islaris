From isla Require Import isla_lang.

Definition a7414 : list trc := [
  [
    Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 28%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
    Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "SP"] (Val_Struct [("SP", Val_Bits [BV{1%N} 0x1%Z])]) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
    ReadReg "SP_EL2" [] (Val_Symbolic 29%Z) Mk_annot;
    ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
    Smt (DefineConst 73%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 74%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 78%Z (Binop (Eq) (Val (Val_Symbolic 74%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 74%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Val (Val_Symbolic 74%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 74%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Symbolic 28%Z)]) Mk_annot;
    Smt (DefineConst 290%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 290%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 290%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 293%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 293%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 293%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
    ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 74%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 905%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 905%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 905%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 908%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 908%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 908%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 937%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 937%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 937%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 940%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 940%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 940%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 979%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 979%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 979%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1187%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1187%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1187%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1190%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1190%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1190%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1229%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1229%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1229%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1232%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1232%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1232%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "D"] (Val_Struct [("D", Val_Symbolic 6%Z)]) Mk_annot;
    ReadReg "OSLSR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
    ReadReg "OSDLR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
    ReadReg "EDSCR" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
    Smt (DefineConst 1267%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1267%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1267%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1270%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1270%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1270%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1312%Z (Ty_BitVec 56%N)) Mk_annot;
    Smt (DefineConst 1321%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 74%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1322%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadMem (Val_Symbolic 1322%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 1321%Z) 8%N None Mk_annot;
    Smt (DefineConst 1324%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1324%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1324%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1327%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 1331%Z (Binop (Eq) (Val (Val_Symbolic 1327%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1327%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1331%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1331%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Val (Val_Symbolic 1327%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1327%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1522%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1522%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1522%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 1525%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1525%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 1525%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 1327%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2137%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2137%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2137%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2140%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2140%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2140%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2169%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2169%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2169%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2172%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2172%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2172%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2211%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2211%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2211%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1331%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2419%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2419%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2419%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2422%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2422%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2422%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2461%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2461%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2461%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2464%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2464%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2464%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2499%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2499%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2499%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2502%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2502%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2502%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2544%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1327%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 2545%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadMem (Val_Symbolic 2545%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 2544%Z) 8%N None Mk_annot;
    Smt (DefineConst 2547%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2547%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 2547%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2550%Z (Val (Val_Symbolic 1322%Z) Mk_annot)) Mk_annot;
    WriteReg "R0" [] (Val_Symbolic 2550%Z) Mk_annot;
    Smt (DefineConst 2551%Z (Val (Val_Symbolic 2545%Z) Mk_annot)) Mk_annot;
    WriteReg "R1" [] (Val_Symbolic 2551%Z) Mk_annot
  ]
].
