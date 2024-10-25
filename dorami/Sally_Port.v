Require Import isla.riscv64.riscv64.
From isla.dorami.instructions.Sally_Port Require Import instrs.

Definition Sally_Port_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
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
Arguments Sally_Port_spec /.

Lemma Sally_Port `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  instr 0x0000000010300028 (Some a28) -∗
  instr_body 0x0000000010300000 Sally_Port_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.
