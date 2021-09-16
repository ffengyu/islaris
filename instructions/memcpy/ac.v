From isla Require Import isla_lang.

Definition ac : list trc := [
  [
    Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
    Smt (DeclareConst 30%Z (Ty_BitVec 64%N)) Mk_annot;
    Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Symbolic 30%Z) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "R3" [] (RegVal_Base (Val_Symbolic 30%Z)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot;
    Smt (DefineConst 103%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Symbolic 30%Z) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 104%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R4" [] (RegVal_Base (Val_Symbolic 104%Z)) Mk_annot;
    Smt (DefineConst 105%Z (Unop (Extract 7%N 0%N) (Val (Val_Symbolic 104%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    Smt (DefineConst 110%Z (Binop (Eq) (Val (Val_Symbolic 103%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 103%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffff%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 110%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 110%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Val (Val_Symbolic 103%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 103%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffff%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 103%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 110%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot;
    ReadReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 1233%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 1233%Z)) Mk_annot;
    Smt (DeclareConst 1302%Z (Ty_BitVec 56%N)) Mk_annot;
    Smt (DefineConst 1315%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 103%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1316%Z Ty_Bool) Mk_annot;
    WriteMem (RegVal_Base (Val_Symbolic 1316%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 7%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 1315%Z)) (RegVal_Base (Val_Symbolic 105%Z)) 1%N None Mk_annot
  ]
].
