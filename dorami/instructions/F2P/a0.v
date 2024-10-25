From isla Require Import opsem.

Definition a0 : isla_trace :=
  AssumeReg "rv_enable_zfinx" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  Smt (DeclareConst 0%Z (Ty_Enum "Privilege")) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "misa" [Field "bits"]) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x800000000015312d%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot :t:
  Smt (DefineConst 3%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 2%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "cur_privilege" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 14%Z))]) Mk_annot :t:
  Smt (DefineConst 15%Z (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 14%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff7%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 14%Z))]) Mk_annot :t:
  Smt (DefineConst 24%Z (Manyop (Bvmanyarith Bvand) [Unop (ZeroExtend 41%N) (Manyop Concat [Unop (Extract 22%N 7%N) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot; Manyop Concat [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Manyop Concat [Unop (Extract 5%N 3%N) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot; Manyop Concat [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 1%N 0%N) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot] Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffe7fff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 25%Z (Unop (Extract 14%N 13%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 27%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 25%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 27%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 29%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 25%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 29%Z) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 31%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 25%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
      tcases [
        Smt (Assert (Val (Val_Symbolic 31%Z) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 37%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
        ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
        WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 37%Z))]) Mk_annot :t:
        ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 37%Z))]) Mk_annot :t:
        WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
        tnil;
        Smt (Assert (Unop (Not) (Val (Val_Symbolic 31%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 47%Z (Unop (Extract 10%N 9%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 49%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 47%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
        tcases [
          Smt (Assert (Val (Val_Symbolic 49%Z) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 51%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 47%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
          tcases [
            Smt (Assert (Val (Val_Symbolic 51%Z) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 53%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 47%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
            tcases [
              Smt (Assert (Val (Val_Symbolic 53%Z) Mk_annot)) Mk_annot :t:
              Smt (DefineConst 59%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
              ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
              WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 59%Z))]) Mk_annot :t:
              ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 59%Z))]) Mk_annot :t:
              WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
              tnil;
              Smt (Assert (Unop (Not) (Val (Val_Symbolic 53%Z) Mk_annot) Mk_annot)) Mk_annot :t:
              Smt (DefineConst 71%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
              ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
              WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 71%Z))]) Mk_annot :t:
              ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 71%Z))]) Mk_annot :t:
              WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
              tnil
            ];
            Smt (Assert (Unop (Not) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 83%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
            ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
            WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 83%Z))]) Mk_annot :t:
            ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 83%Z))]) Mk_annot :t:
            WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
            tnil
          ];
          Smt (Assert (Unop (Not) (Val (Val_Symbolic 49%Z) Mk_annot) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 95%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 95%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 95%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
          tnil
        ]
      ];
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 105%Z (Unop (Extract 10%N 9%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 107%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 105%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
      tcases [
        Smt (Assert (Val (Val_Symbolic 107%Z) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 109%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 105%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
        tcases [
          Smt (Assert (Val (Val_Symbolic 109%Z) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 111%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 105%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
          tcases [
            Smt (Assert (Val (Val_Symbolic 111%Z) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 117%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
            ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
            WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 117%Z))]) Mk_annot :t:
            ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 117%Z))]) Mk_annot :t:
            WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
            tnil;
            Smt (Assert (Unop (Not) (Val (Val_Symbolic 111%Z) Mk_annot) Mk_annot)) Mk_annot :t:
            Smt (DefineConst 129%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
            ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
            WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 129%Z))]) Mk_annot :t:
            ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 129%Z))]) Mk_annot :t:
            WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
            tnil
          ];
          Smt (Assert (Unop (Not) (Val (Val_Symbolic 109%Z) Mk_annot) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 141%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 141%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 141%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
          tnil
        ];
        Smt (Assert (Unop (Not) (Val (Val_Symbolic 107%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 153%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
        ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
        WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 153%Z))]) Mk_annot :t:
        ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 153%Z))]) Mk_annot :t:
        WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
        tnil
      ]
    ];
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 27%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 163%Z (Unop (Extract 10%N 9%N) (Val (Val_Symbolic 24%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 165%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 163%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 165%Z) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 167%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 163%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
      tcases [
        Smt (Assert (Val (Val_Symbolic 167%Z) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 169%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 163%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x2%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
        tcases [
          Smt (Assert (Val (Val_Symbolic 169%Z) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 175%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 175%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 175%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
          tnil;
          Smt (Assert (Unop (Not) (Val (Val_Symbolic 169%Z) Mk_annot) Mk_annot)) Mk_annot :t:
          Smt (DefineConst 187%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
          ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
          WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 187%Z))]) Mk_annot :t:
          ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 187%Z))]) Mk_annot :t:
          WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
          tnil
        ];
        Smt (Assert (Unop (Not) (Val (Val_Symbolic 167%Z) Mk_annot) Mk_annot)) Mk_annot :t:
        Smt (DefineConst 199%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
        ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
        WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 199%Z))]) Mk_annot :t:
        ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 199%Z))]) Mk_annot :t:
        WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
        tnil
      ];
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 165%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 211%Z (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 24%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffff3ffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 35%N 34%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x22%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffcffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 62%N) (Unop (Extract 33%N 32%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffcfffffffff%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      ReadReg "misa" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
      WriteReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 211%Z))]) Mk_annot :t:
      ReadReg "mstatus" [Field "bits"] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 211%Z))]) Mk_annot :t:
      WriteReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
      tnil
    ]
  ]
.
