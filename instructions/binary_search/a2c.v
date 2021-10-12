From isla Require Import isla_lang.

Definition a2c : list trc := [
  [
    Smt (DeclareConst 42%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R20" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot;
    Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R23" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot;
    Smt (DefineConst 74%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 42%Z) Mk_annot) Mk_annot) Mk_annot; Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Unop (Bvnot) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R8" [] (RegVal_Base (Val_Symbolic 74%Z)) Mk_annot;
    Smt (DeclareConst 75%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 75%Z)) Mk_annot;
    Smt (DefineConst 76%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 75%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 76%Z)) Mk_annot
  ]
].
