Require Import isla.riscv64.riscv64.
From isla.instructions.add Require Import instrs.

Definition test_add_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (r : addr),
    reg_col sys_regs ∗
    "x10" ↦ᵣ RVal_Bits (BV 64 0) ∗
    instr_pre (bv_unsigned r) (
      reg_col sys_regs ∗
      "x10" ↦ᵣ RVal_Bits (BV 64 3) ∗ True
    ).
Arguments test_add_spec /.

Lemma test_state_iris_fn1 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300010 (Some a0) -∗
  instr 0x0000000010300014 (Some a4) -∗
  instr_body 0x0000000010300010 test_add_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.
