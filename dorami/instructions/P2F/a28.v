From isla Require Import opsem.

Definition a28 : isla_trace :=
  AssumeReg "rv_pmp_count" [] (RegVal_I 16%Z 64%Z) Mk_annot :t:
  AssumeReg "rv_pmp_grain" [] (RegVal_I 10%Z 64%Z) Mk_annot :t:
  Smt (DeclareConst 0%Z (Ty_Enum "Privilege")) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "x5" []) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x989b989d981e%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp0cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x1e%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp1cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x9d%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 4%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp2cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x98%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 5%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp3cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x98%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 6%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp4cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x98%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 7%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp5cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x9b%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 8%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp6cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 9%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp7cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 10%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "mseccfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x7%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 11%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 11%Z)) Mk_annot :t:
  Smt (DefineConst 12%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 11%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "x5" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  ReadReg "cur_privilege" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  ReadReg "rv_pmp_count" [] (RegVal_I 16%Z 64%Z) Mk_annot :t:
  ReadReg "pmp7cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 9%Z))]) Mk_annot :t:
  ReadReg "pmp6cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 8%Z))]) Mk_annot :t:
  ReadReg "pmp5cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 7%Z))]) Mk_annot :t:
  ReadReg "pmp4cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot :t:
  ReadReg "pmp3cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot :t:
  ReadReg "pmp2cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 4%Z))]) Mk_annot :t:
  ReadReg "pmp1cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
  ReadReg "pmp0cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 2%Z))]) Mk_annot :t:
  Smt (DefineConst 31%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 7%N 0%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "mseccfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 10%Z))]) Mk_annot :t:
  ReadReg "rv_pmp_grain" [] (RegVal_I 10%Z 64%Z) Mk_annot :t:
  Smt (DefineConst 42%Z (Unop (Extract 4%N 3%N) (Val (Val_Symbolic 2%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "pmp0cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 31%Z))]) Mk_annot :t:
  Smt (DefineConst 50%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 15%N 8%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 63%Z (Unop (Extract 4%N 3%N) (Val (Val_Symbolic 3%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "pmp1cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 50%Z))]) Mk_annot :t:
  Smt (DefineConst 71%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 23%N 16%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 84%Z (Unop (Extract 4%N 3%N) (Val (Val_Symbolic 4%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "pmp2cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 71%Z))]) Mk_annot :t:
  Smt (DefineConst 92%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 24%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 105%Z (Unop (Extract 4%N 3%N) (Val (Val_Symbolic 5%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "pmp3cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 92%Z))]) Mk_annot :t:
  Smt (DefineConst 113%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 39%N 32%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 126%Z (Unop (Extract 4%N 3%N) (Val (Val_Symbolic 6%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "pmp4cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 113%Z))]) Mk_annot :t:
  Smt (DefineConst 134%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 47%N 40%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 147%Z (Unop (Extract 4%N 3%N) (Val (Val_Symbolic 7%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "pmp5cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 134%Z))]) Mk_annot :t:
  Smt (DefineConst 155%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 55%N 48%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "pmp6cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 155%Z))]) Mk_annot :t:
  Smt (DefineConst 170%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 63%N 56%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 8%N 0x9f%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "pmp7cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 170%Z))]) Mk_annot :t:
  ReadReg "pmp7cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 170%Z))]) Mk_annot :t:
  ReadReg "pmp6cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 155%Z))]) Mk_annot :t:
  ReadReg "pmp5cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 134%Z))]) Mk_annot :t:
  ReadReg "pmp4cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 113%Z))]) Mk_annot :t:
  ReadReg "pmp3cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 92%Z))]) Mk_annot :t:
  ReadReg "pmp2cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 71%Z))]) Mk_annot :t:
  ReadReg "pmp1cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 50%Z))]) Mk_annot :t:
  ReadReg "pmp0cfg" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 31%Z))]) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
  tnil
.
