From isla Require Import isla_lang.

Definition a5c : list trc := [
  [
    Smt (DeclareConst 48%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R23" [] (Val_Symbolic 48%Z) Mk_annot;
    Smt (DefineConst 54%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot; Val (Val_Symbolic 48%Z) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R0" [] (Val_Symbolic 54%Z) Mk_annot
  ]
].