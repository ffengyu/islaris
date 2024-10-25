Require Import isla.riscv64.riscv64.

(* TODO: reg_col for GPR and PMP? How about other CSR? *)
(* TODO: list the perm fro mem and inst for the fixed region. *)
(* TODO: use instr directly instead of instr_table. *)
Definition MStep_pre `{!islaG Σ} `{!threadG} (h i: bv 64) (entries: list (bv 64 * bv 8)): iProp Σ :=
  arch_pc_reg ↦ᵣ RVal_Bits i ∗ (∃ tbl t, instr_table tbl ∗ ⌜tbl !! i = Some t⌝) ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗ (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me) ∗
  reg_col (pmp_regs entries) ∗ interp_pmp entries "Machine".

(* Can it be NONE? probably no. *)
(* Two instr at same addr is allowed. *)
(* TODO: reuse the MStep_pre definition. *)
Definition PMPHold `{!islaG Σ} `{!threadG} (h: bv 64) (entries: list (bv 64 * bv 8)) : iProp Σ :=
  (∃ (i: bv 64) tbl t, arch_pc_reg ↦ᵣ RVal_Bits i ∗ instr_table tbl ∗ ⌜tbl !! i = Some t⌝) ∗
  "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗ "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me) ∗
  reg_col (pmp_regs entries) ∗ interp_pmp entries "Machine".

Fixpoint NoPMPWrite (t: isla_trace) : bool :=
  match t with
  | tnil => true
  | tcons (WriteReg regname _ _ _) t => negb (String.prefix "pmp" regname) && NoPMPWrite t
  | tcons _ t => NoPMPWrite t
  | tcases ts => foldr (λ t b, NoPMPWrite t && b) true ts
  end.

Definition PMPMod `{!islaG Σ} `{!threadG} : iProp Σ :=
  (∃ (i: bv 64) tbl t, arch_pc_reg ↦ᵣ RVal_Bits i ∗ instr_table tbl ∗ ⌜tbl !! i = Some t⌝ ∗ ⌜negb (NoPMPWrite t)⌝) ∗
  "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  (∃ h, "mtvec" # "bits" ↦ᵣ RVal_Bits h) ∗ (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me) ∗
  (∃ entries, reg_col (pmp_regs entries) ∗ interp_pmp entries "Machine").

(* Should have the "instr h (Some t)" *)
Definition MTrap `{!islaG Σ} `{!threadG} (h: bv 64) (entries: list (bv 64 * bv 8)): iProp Σ :=
  arch_pc_reg ↦ᵣ RVal_Bits h ∗ (∃ tbl t, instr_table tbl ∗ ⌜tbl !! h = Some t⌝) ∗ "cur_privilege" ↦ᵣ RVal_Enum "Machine" ∗
  "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗ (∃ mc, "mcause" # "bits" ↦ᵣ RVal_Bits mc) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me) ∗
  reg_col (pmp_regs entries) ∗ interp_pmp entries "Machine".

(* Should have the "instr i (Some t)" *)
Definition MRecover `{!islaG Σ} `{!threadG} (h: bv 64) (entries: list (bv 64 * bv 8)): iProp Σ :=
  (∃ (i: bv 64) tbl t, arch_pc_reg ↦ᵣ RVal_Bits i ∗ instr_table tbl ∗ ⌜tbl !! i = Some t⌝ ∗ "mepc" ↦ᵣ RVal_Bits i) ∗
  "cur_privilege" ↦ᵣ RVal_Enum "User" ∗ "mtvec" # "bits" ↦ᵣ RVal_Bits h ∗
  (∃ c, "mcause" # "bits" ↦ᵣ RVal_Bits c) ∗
  (∃ ms, "mstatus" # "bits" ↦ᵣ RVal_Bits ms) ∗ (∃ me, "mepc" ↦ᵣ RVal_Bits me) ∗
  reg_col (pmp_regs entries) ∗ interp_pmp entries "User".

Definition step_contract `{!islaG Σ} `{!threadG} :=
  ∀ t h i entries,
  ((PMPHold h entries
    ∨ PMPMod
    ∨ MTrap h entries
    ∨ MRecover h entries) -∗ WPasm tnil) -∗
  (MStep_pre h i entries -∗ WPasm t).

Definition cycle_precond  `{!islaG Σ} `{!threadG} h i entries : iProp Σ :=
  MStep_pre h i entries ∗
  ▷(PMPMod -∗ WPasm tnil) ∗
  ▷(MTrap h entries -∗ WPasm tnil) ∗
  ▷(MRecover h entries -∗ WPasm tnil).

Definition cycle_contract `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∀ h i entries,
   (cycle_precond h i entries) -∗
   WPasm tnil.

(* Implicit Arg in Hypothesis *)

Section universal_contract.
Context `{!islaG Σ} `{!threadG}.
(* How to remove the context *)
Hypothesis valid_step_contract :
  step_contract.

Lemma valid_cycle_contract : ⊢ cycle_contract.
Proof using valid_step_contract.
  iLöb as "IH".
  iIntros (h i entries) "(Hpre & HCSRMod & HTrap & HRecover)".
  iDestruct "Hpre" as "(Hpc&(%tbl & %t & #Hinstbl & %Hlkins)&?&?&?&?&?&?&?)".
  Check instr_intro.
  iPoseProof (instr_intro _ _ _ _ Hlkins with "Hinstbl") as "Hinst".
  iApply (wp_next_instr i with "[$Hpc] [Hinst]"); first by iFrame.
  iModIntro.
  iIntros "Hpc".
  iApply (valid_step_contract t h i entries with "[HCSRMod HTrap HRecover]"); last (iFrame; by auto).
  iIntros "[HRes | [HRes | [HRes | HRes]]]".
  - iDestruct "HRes" as "((%i' & %tbl' & %t' & Hpc' & #Hinstbl' & %Hlkins') &?&?&?&?&?)".
    iApply "IH". iFrame. by auto.
  - by iApply "HCSRMod".
  - by iApply "HTrap".
  - by iApply "HRecover".
  Unshelve.
  apply bv_is_wf.
Qed.

Lemma firmware_safety F2P F_start entries :
  MStep_pre F2P F_start entries -∗
  (∃ tbl, instr_table tbl ∗ ⌜map_Forall (λ _ t, NoPMPWrite t) tbl⌝) -∗
  ("cur_privilege" ↦ᵣ RVal_Enum "User" -∗
   (∀ i, instr i None) ∗ "cur_privilege" ↦ᵣ RVal_Enum "User") -∗ (*TODO: derived from interp_pmp *)
  (MTrap F2P entries -∗ WPasm tnil) -∗
  WPasm tnil.
Proof using  valid_step_contract.
  iIntros "? #HNoPMPWrite HNoUserInst HTrap".
  iApply valid_cycle_contract.
  iFrame.
  iSplitR.
  - iIntros "!> ((%i & %tbl & %t & ? & #Hinstbl & %Hinst & %HPMPWrite)&?&?&?&?&?&?)".
    iDestruct "HNoPMPWrite" as "(%tbl' & Hinstbl' & %Hallinst)".
    iPoseProof (instr_table_agree with "Hinstbl' Hinstbl") as "->".
    assert (NoPMPWrite t) by exact (map_Forall_lookup_1 _ _ _ _ Hallinst Hinst).
    destruct (NoPMPWrite t); by simpl in *.
  - iIntros "!> ((%i & %tbl & %t & ? & #Hinstbl & %Hinst & Hmepc)&?&?&?&?&?&?&?)".
    iPoseProof ("HNoUserInst" with "[$]") as "[HNoInst _]".
    iSpecialize ("HNoInst" $! (bv_unsigned i)).
    iPoseProof (instr_lookup with "Hinstbl HNoInst") as "%HH".
    destruct HH as (b & Hb & Hinst').
    assert (Z_to_bv_checked 64 (bv_unsigned i) = Some i) by (apply Z_to_bv_checked_bv_unsigned).
    rewrite H0 in Hb.
    inversion Hb.
    rewrite -H2 in Hinst'.
    rewrite Hinst' in Hinst.
    inversion Hinst.
Qed.

End universal_contract.
