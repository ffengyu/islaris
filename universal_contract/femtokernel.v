Require Import isla.riscv64.riscv64.

Context `{!islaG Σ} `{!threadG}.

(* reg_col for GPR and PMP? How about other CSR? *)
Definition Step_pre m (h i mpp: bv 64) : iProp Σ :=
  arch_pc_reg ↦ᵣ RVal_Bits i ∗ "cur_privilege" ↦ᵣ RVal_Enum m ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗ (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  "mstatus" # "bits" ↦ᵣ RVal_Bits mpp ∗ (∃ c, "mepc" ↦ᵣ RVal_Bits c).

(* Can it be NONE? probably no. *)
Definition Execution (inst_trace: gmap (bv 64) isla_trace) m (h mpp: bv 64) : iProp Σ :=
  (∃ (i: bv 64) t, arch_pc_reg ↦ᵣ RVal_Bits i ∗ ⌜inst_trace !! i = Some t⌝) ∗
  "cur_privilege" ↦ᵣ RVal_Enum m ∗ "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  "mstatus" # "bits" ↦ᵣ RVal_Bits mpp ∗ (∃ c, "mepc" ↦ᵣ RVal_Bits c).

(* Add inst_trace parameter to CSRMod, Trap, and Recover. *)
Definition CSRMod m : iProp Σ :=
  (∃ i, arch_pc_reg ↦ᵣ RVal_Bits i) ∗ ⌜m = "Machine"⌝ ∗ "cur_privilege" ↦ᵣ RVal_Enum m ∗
  (∃ h, "mtvec" # "bits" ↦ᵣ RVal_Bits h) ∗ (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me).

Definition Trap (h: bv 64) : iProp Σ :=
  arch_pc_reg ↦ᵣ RVal_Bits h ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗ (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  "mstatus" # "bits" ↦ᵣ RVal_Bits (BV 64 0x0000000000000000)  ∗ (∃ c, "mepc" ↦ᵣ RVal_Bits c).

Definition Recover  m (h: bv 64) : iProp Σ :=
  (∃ i, arch_pc_reg ↦ᵣ RVal_Bits i ∗ "mepc" ↦ᵣ RVal_Bits i) ∗ ⌜m = "Machine" ⌝ ∗
  "cur_privilege" ↦ᵣ RVal_Enum "User" ∗ "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  "mstatus" # "bits" ↦ᵣ RVal_Bits (BV 64 0x0000000000000000) ∗ (∃ c, "mepc" ↦ᵣ RVal_Bits c).

Definition step_contract :=
  ∀ inst_trace t m h i mpp,
  (([∗ map] inst ↦ trace ∈ inst_trace, (instr (bv_unsigned inst) (Some trace)))
   ∗ ⌜inst_trace !! i = Some t⌝)-∗
  ((Execution inst_trace m h mpp
    ∨ CSRMod m
    ∨ Trap h
    ∨ Recover m h) -∗ WPasm tnil) -∗
  (Step_pre m h i mpp -∗ WPasm t).

Definition cycle_precond m h i mpp : iProp Σ :=
  Step_pre m h i mpp ∗
  (CSRMod m -∗ WPasm tnil) ∗
  (Trap h -∗ WPasm tnil) ∗
  (Recover m h -∗ WPasm tnil).

Definition cycle_contract : iProp Σ :=
  ∀ m h i mpp,
  (∃ inst_trace t, ([∗ map] inst ↦ trace ∈ inst_trace, instr (bv_unsigned inst) (Some trace))
     ∗ ⌜inst_trace !! i = Some t⌝) -∗
   (cycle_precond m h i mpp) -∗
   WPasm tnil.

(* Implicit Arg in Hypothesis *)
Hypothesis valid_step_contract :
  step_contract.

Lemma valid_cycle_contract : ⊢ cycle_contract.
Proof.
  iLöb as "IH".
  iIntros (m h i mpp) "(%inst_trace & %t & #Hinst_trace & %Hinst) (Hpre & HCSRMod & HTrap & HRecover)".
  iDestruct "Hpre" as "(Hpc&?&?&?&?&?)".
  iApply (wp_next_instr i with "[$Hpc] [Hinst_trace]");
  first iPoseProof (big_sepM_lookup_acc _ _ _ _ Hinst with "[$Hinst_trace]") as "[$ _]".
  iModIntro.
  iIntros "Hpc".
  iApply (valid_step_contract inst_trace t m h i mpp with "[$Hinst_trace //] [HCSRMod HTrap HRecover] [$]").
  iIntros "[HRes | [HRes | [HRes | HRes]]]".
  - iDestruct "HRes" as "((%i' & %t' & Hpc & %Hinst')&?&?&?&?&?)".
    iApply ("IH" with "[$Hinst_trace]"); first by auto.
    iFrame.
  - by iApply "HCSRMod".
  - by iApply "HTrap".
  - by iApply "HRecover".
Qed.
