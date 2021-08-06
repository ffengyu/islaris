From isla Require Import isla_lang.

Definition stp_trace : trc := [
  Smt (DeclareConst 10%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 12%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Binop ((Bvcomp Bvugt)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x10%Z]) Mk_annot) Mk_annot)) Mk_annot;
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1442%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "PSTATE" [Field "SP"] (Val_Struct [("SP", Val_Bits [BV{1%N} 0x1%Z])]) Mk_annot;
  ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
  ReadReg "SP_EL2" [] (Val_Symbolic 29%Z) Mk_annot;
  ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
  Smt (DefineConst 73%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff0%Z]) Mk_annot] Mk_annot)) Mk_annot;
  Smt (DeclareConst 74%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R0" [] (Val_Symbolic 74%Z) Mk_annot;
  Smt (DefineConst 75%Z (Val (Val_Symbolic 74%Z) Mk_annot)) Mk_annot;
  Smt (DeclareConst 76%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R1" [] (Val_Symbolic 76%Z) Mk_annot;
  Smt (DefineConst 77%Z (Val (Val_Symbolic 76%Z) Mk_annot)) Mk_annot;
  Smt (DefineConst 78%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
(*  ReadReg "__v84_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Symbolic 10%Z)]) Mk_annot;
  Smt (DefineConst 80%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 80%Z) Mk_annot) Mk_annot)) Mk_annot;
(*  ReadReg "__highest_el_aarch32" [] (Val_Bool false) Mk_annot;*)
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 80%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 85%Z (Binop (Eq) (Val (Val_Symbolic 78%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 78%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 85%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 85%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Binop (Eq) (Val (Val_Symbolic 78%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 78%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 296%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 296%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 296%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 299%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 299%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 299%Z) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v81_implemented" [] (Val_Bool true) Mk_annot;*)
  ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v83_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 911%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 911%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 911%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 914%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 914%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 914%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 943%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 943%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 943%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 946%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 946%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 946%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 985%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 985%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 985%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 85%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1193%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1193%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1193%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1196%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1196%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1196%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1235%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1235%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1235%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1238%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1238%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1238%Z) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "D"] (Val_Struct [("D", Val_Symbolic 12%Z)]) Mk_annot;
  ReadReg "OSLSR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "OSDLR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "EDSCR" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  Smt (DeclareConst 1251%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "MPIDR_EL1" [] (Val_Symbolic 1251%Z) Mk_annot;
  Smt (DefineConst 1282%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1282%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1282%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1285%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1285%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1285%Z) Mk_annot) Mk_annot)) Mk_annot;
(*  ReadReg "__v82_implemented" [] (Val_Bool false) Mk_annot;*)
(*  ReadReg "__trickbox_enabled" [] (Val_Bool false) Mk_annot;*)
(*  ReadReg "__CNTControlBase" [] (Val_Bits [BV{52%N} 0x0%Z]) Mk_annot;*)
  Smt (DeclareConst 1325%Z (Ty_BitVec 56%N)) Mk_annot;
(*  ReadReg "__defaultRAM" [] (Val_Symbolic 1325%Z) Mk_annot;*)
(*  ReadReg "__isla_monomorphize_writes" [] (Val_Bool false) Mk_annot;*)
  Smt (DefineConst 1338%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DeclareConst 1339%Z Ty_Bool) Mk_annot;
  WriteMem (Val_Symbolic 1339%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 1338%Z) (Val_Symbolic 75%Z) 8%N None Mk_annot;
  Smt (DefineConst 1340%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot)) Mk_annot;
  Smt (DefineConst 1342%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1342%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1342%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1347%Z (Binop (Eq) (Val (Val_Symbolic 1340%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1340%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1347%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1347%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Binop (Eq) (Val (Val_Symbolic 1340%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1340%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1537%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1537%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1537%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1540%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1540%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1540%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 1340%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2152%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2152%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2152%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2155%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2155%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2155%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2184%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2184%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2184%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2187%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2187%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2187%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2226%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2226%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2226%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1347%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2434%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2434%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2434%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2437%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2437%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2437%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2476%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2476%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2476%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2479%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2479%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2479%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2522%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2522%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2522%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2525%Z (Binop (Eq) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2525%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 2525%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 2565%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1340%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DeclareConst 2566%Z Ty_Bool) Mk_annot;
  WriteMem (Val_Symbolic 2566%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 2565%Z) (Val_Symbolic 77%Z) 8%N None Mk_annot;
  Smt (DefineConst 2567%Z (Val (Val_Symbolic 73%Z) Mk_annot)) Mk_annot;
  WriteReg "SP_EL2" [] (Val_Symbolic 2567%Z) Mk_annot
].
