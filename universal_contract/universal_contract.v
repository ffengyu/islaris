Require Import isla.riscv64.riscv64.

(* reg_col for GPR and PMP? How about other CSR? *)
Definition MStep_pre `{!islaG Σ} `{!threadG} (h i: bv 64) (entries: list (bv 64 * bv 8)): iProp Σ :=
  arch_pc_reg ↦ᵣ RVal_Bits i ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗ (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me) ∗
  reg_col (pmp_regs entries) ∗ interp_pmp entries "Machine".

(* Can it be NONE? probably no. *)
Definition PMPHold  `{!islaG Σ} `{!threadG} (inst_trace: gmap (bv 64) isla_trace) (h: bv 64) : iProp Σ :=
  (∃ (i: bv 64) t, arch_pc_reg ↦ᵣ RVal_Bits i ∗ ⌜inst_trace !! i = Some t⌝) ∗
  "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗ "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me).

Fixpoint NoPMPWrite (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (WriteReg regname _ _ _) t => negb (String.prefix "pmp" regname) && NoPMPWrite t
  | tcons _ t => NoPMPWrite t
  | tcases ts => foldr (λ t b, NoPMPWrite t && b) true ts
  end.

(* The instr can also be in pmp_acces *)
Definition PMPMod : iProp Σ :=
  (∃ (i: bv 64) t, arch_pc_reg ↦ᵣ RVal_Bits i ∗ instr (bv_unsigned i) (Some t) ∗ ⌜NoPMPWrite t⌝) ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  (∃ h, "mtvec" # "bits" ↦ᵣ RVal_Bits h) ∗ (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me).

Definition MTrap (h: bv 64) : iProp Σ :=
  arch_pc_reg ↦ᵣ RVal_Bits h ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗ (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me).

Definition MRecover (h: bv 64) : iProp Σ :=
  (∃ i, arch_pc_reg ↦ᵣ RVal_Bits i ∗ "mepc" ↦ᵣ RVal_Bits i) ∗
  "cur_privilege" ↦ᵣ RVal_Enum "User" ∗ "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me).

Definition step_contract :=
  ∀ inst_trace t h i,
  (([∗ map] inst ↦ trace ∈ inst_trace, (instr (bv_unsigned inst) (Some trace)))
   ∗ ⌜inst_trace !! i = Some t⌝)-∗
  ((PMPHold inst_trace h
    ∨ PMPMod
    ∨ MTrap h
    ∨ MRecover h) -∗ WPasm tnil) -∗
  (MStep_pre h i -∗ WPasm t).

Definition cycle_precond h i : iProp Σ :=
  MStep_pre h i ∗
  (PMPMod -∗ WPasm tnil) ∗
  (MTrap h -∗ WPasm tnil) ∗
  (MRecover h -∗ WPasm tnil).

Definition cycle_contract : iProp Σ :=
  ∀ h i,
  (∃ inst_trace t, ([∗ map] inst ↦ trace ∈ inst_trace, instr (bv_unsigned inst) (Some trace))
     ∗ ⌜inst_trace !! i = Some t⌝) -∗
   (cycle_precond h i) -∗
   WPasm tnil.

(* Implicit Arg in Hypothesis *)
Hypothesis valid_step_contract :
  step_contract.

Lemma valid_cycle_contract : ⊢ cycle_contract.
Proof.
  iLöb as "IH".
  iIntros (h i) "(%inst_trace & %t & #Hinst_trace & %Hinst) (Hpre & HCSRMod & HTrap & HRecover)".
  iDestruct "Hpre" as "(Hpc&?&?&?&?&?)".
  iApply (wp_next_instr i with "[$Hpc] [Hinst_trace]");
  first iPoseProof (big_sepM_lookup_acc _ _ _ _ Hinst with "[$Hinst_trace]") as "[$ _]".
  iModIntro.
  iIntros "Hpc".
  iApply (valid_step_contract inst_trace t h i with "[$Hinst_trace //] [HCSRMod HTrap HRecover] [$]").
  iIntros "[HRes | [HRes | [HRes | HRes]]]".
  - iDestruct "HRes" as "((%i' & %t' & Hpc & %Hinst')&?&?&?&?&?)".
    iApply ("IH" with "[$Hinst_trace]"); first by auto.
    iFrame.
  - by iApply "HCSRMod".
  - by iApply "HTrap".
  - by iApply "HRecover".
Qed.

Parameter firmware_code_range : prod Z Z.
Parameter firmware_mem_range : prod Z Z.
