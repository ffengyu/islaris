Require Import isla.riscv64.riscv64.
From isla.dorami.instructions.exit_firmware Require Import instrs.

Definition P2F_spec' `{!islaG Σ} `{!threadG} : iProp Σ :=
    reg_col sys_regs ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0) ∗
    "mtvec" # "bits" ↦ᵣ RVal_Bits (BV 64 0) ∗
    "mseccfg" # "bits" ↦ᵣ RVal_Bits (BV 64 0x0000000000000007) ∗
    "pmp0cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp1cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp2cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp3cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp4cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp5cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp6cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    "pmp7cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0) ∗
    instr_pre 0x000000001030002c (
      reg_col sys_regs ∗
      "mtvec" # "bits" ↦ᵣ RVal_Bits (BV 64 0x0000000080020000) ∗
      "pmp0cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0x1e) ∗
      "pmp1cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0x98) ∗
      "pmp2cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0x9d) ∗
      "pmp3cfg" # "bits" ↦ᵣ RVal_Bits(BV 8 0x98) ∗
      "pmp4cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0x9b) ∗
      "pmp5cfg" # "bits" ↦ᵣ RVal_Bits (BV 8 0x98) ∗
      True
    ).
Arguments P2F_spec' /.

Lemma P2F' `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr_body 0x0000000010300000 P2F_spec'.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.
