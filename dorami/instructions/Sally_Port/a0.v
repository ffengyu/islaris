From isla Require Import opsem.

Definition a0 : isla_trace :=
  AssumeReg "rv_enable_zfinx" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  Smt (DeclareConst 0%Z (Ty_Enum "Privilege")) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "misa" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x800000000015312d%Z)) Mk_annot) Mk_annot) Mk_annot :t:
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
  ReadReg "cur_privilege" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DeclareConst 23%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
  Smt (DefineConst 24%Z (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 23%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff7%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
  Smt (DefineConst 33%Z (Manyop (Bvmanyarith Bvand) [Unop (ZeroExtend 41%N) (Manyop Concat [Unop (Extract 22%N 7%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot; Manyop Concat [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Manyop Concat [Unop (Extract 5%N 3%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot; Manyop Concat [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 1%N 0%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot] Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffe7fff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 34%Z (Unop (Extract 14%N 13%N) (Val (Val_Symbolic 33%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 36%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 34%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 36%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 38%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 34%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 40%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 34%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
      tcases [
        Smt (Assert (Val (Val_Symbolic 40%Z) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 46%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
        ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
        WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 46%Z))]) Mk_annot :t:
        ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 46%Z))]) Mk_annot :t:
        WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
        tnil;
        Smt (Assert (Unop (Not) (Val (Val_Symbolic 40%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 56%Z (Unop (Extract 10%N 9%N) (Val (Val_Symbolic 33%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 58%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 56%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
        tcases [
          Smt (Assert (Val (Val_Symbolic 58%Z) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 60%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 56%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
          tcases [
            Smt (Assert (Val (Val_Symbolic 60%Z) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 62%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 56%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
            tcases [
              Smt (Assert (Val (Val_Symbolic 62%Z) Mk_annot)) Mk_annot :t:
              Smt (DefineConst 68%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
              ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
              WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 68%Z))]) Mk_annot :t:
              ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 68%Z))]) Mk_annot :t:
              WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
              tnil;
              Smt (Assert (Unop (Not) (Val (Val_Symbolic 62%Z) Mk_annot) Mk_annot)) Mk_annot :t:
              Smt (DefineConst 80%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
              ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
              WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 80%Z))]) Mk_annot :t:
              ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 80%Z))]) Mk_annot :t:
              WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
              tnil
            ];
            Smt (Assert (Unop (Not) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 92%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
            ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
            WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 92%Z))]) Mk_annot :t:
            ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 92%Z))]) Mk_annot :t:
            WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
            tnil
          ];
          Smt (Assert (Unop (Not) (Val (Val_Symbolic 58%Z) Mk_annot) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 104%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 104%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 104%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
          tnil
        ]
      ];
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 114%Z (Unop (Extract 10%N 9%N) (Val (Val_Symbolic 33%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 116%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 114%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
      tcases [
        Smt (Assert (Val (Val_Symbolic 116%Z) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 118%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 114%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
        tcases [
          Smt (Assert (Val (Val_Symbolic 118%Z) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 120%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 114%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
          tcases [
            Smt (Assert (Val (Val_Symbolic 120%Z) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 126%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
            ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
            WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 126%Z))]) Mk_annot :t:
            ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 126%Z))]) Mk_annot :t:
            WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
            tnil;
            Smt (Assert (Unop (Not) (Val (Val_Symbolic 120%Z) Mk_annot) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 138%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
            ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
            WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 138%Z))]) Mk_annot :t:
            ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 138%Z))]) Mk_annot :t:
            WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
            tnil
          ];
          Smt (Assert (Unop (Not) (Val (Val_Symbolic 118%Z) Mk_annot) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 150%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 150%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 150%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
          tnil
        ];
        Smt (Assert (Unop (Not) (Val (Val_Symbolic 116%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 162%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
        ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
        WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 162%Z))]) Mk_annot :t:
        ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 162%Z))]) Mk_annot :t:
        WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
        tnil
      ]
    ];
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 36%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 172%Z (Unop (Extract 10%N 9%N) (Val (Val_Symbolic 33%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 174%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 172%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 174%Z) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 176%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 172%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
      tcases [
        Smt (Assert (Val (Val_Symbolic 176%Z) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 178%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 172%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
        tcases [
          Smt (Assert (Val (Val_Symbolic 178%Z) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 184%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 184%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 184%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
          tnil;
          Smt (Assert (Unop (Not) (Val (Val_Symbolic 178%Z) Mk_annot) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 196%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 196%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 196%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
          tnil
        ];
        Smt (Assert (Unop (Not) (Val (Val_Symbolic 176%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 208%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
        ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
        WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 208%Z))]) Mk_annot :t:
        ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 208%Z))]) Mk_annot :t:
        WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
        tnil
      ];
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 174%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 220%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 33%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 23%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
      WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 220%Z))]) Mk_annot :t:
      ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 220%Z))]) Mk_annot :t:
      WriteReg "PC" [] (RegVal_Base (Val_Symbolic 12%Z)) Mk_annot :t:
      tnil
    ]
  ]
.
