From isla Require Import opsem.

Definition ac : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_Enum "Privilege")) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "x5" []) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x80020000%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot :t:
  Smt (DefineConst 3%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 2%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "x5" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  ReadReg "cur_privilege" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 14%Z))]) Mk_annot :t:
  ReadReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 14%Z))]) Mk_annot :t:
  WriteReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
  ReadReg "mtvec" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  tnil
.
