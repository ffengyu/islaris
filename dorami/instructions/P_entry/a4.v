From isla Require Import opsem.

Definition a4 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x5" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot :t:
  Smt (DefineConst 5%Z (Unop (SignExtend 32%N) (Manyop (Bvmanyarith Bvadd) [Val (Val_Bits (BV 32%N 0x313%Z)) Mk_annot; Unop (Extract 31%N 0%N) (Val (Val_Symbolic 2%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "x5" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  tnil
.
