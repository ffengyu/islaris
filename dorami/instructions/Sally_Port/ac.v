From isla Require Import opsem.

Definition ac : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_Enum "Privilege")) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "x5" []) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x80000000%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp0cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp1cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 4%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp2cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 5%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp3cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 6%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp4cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 7%Z (Ty_BitVec 8%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "pmp5cfg" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 8%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
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
  Smt (DeclareConst 23%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
  ReadReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
  WriteReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
  ReadReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
  tnil
.