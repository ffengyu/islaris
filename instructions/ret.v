From isla Require Import isla_lang.

Definition ret_trace : trc := [
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1522%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (DeclareConst 49%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R30" [] (Val_Symbolic 49%Z) Mk_annot;
  Smt (DefineConst 50%Z (Val (Val_Symbolic 49%Z) Mk_annot)) Mk_annot;
(*  WriteReg "BTypeNext" [] (Val_Bits [BV{2%N} 0x0%Z]) Mk_annot;*)
  ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Bits [BV{1%N} 0x0%Z])]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
(*  ReadReg "__highest_el_aarch32" [] (Val_Bool false) Mk_annot;*)
  Smt (DefineConst 51%Z (Val (Val_Symbolic 50%Z) Mk_annot)) Mk_annot;
  BranchAddress (Val_Symbolic 51%Z) Mk_annot;
  Smt (DefineConst 52%Z (Val (Val_Symbolic 50%Z) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
  ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v81_implemented" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v84_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v83_implemented" [] (Val_Bool false) Mk_annot;*)
  WriteReg "_PC" [] (Val_Symbolic 52%Z) Mk_annot;
  WriteReg "__PC_changed" [] (Val_Bool true) Mk_annot
].
