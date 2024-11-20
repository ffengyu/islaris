Require Import isla.riscv64.riscv64.

Lemma wp_declare_const_bool' `{!islaG Σ} `{!threadG} v es ann:
  (∀ (b : bool), ▷WPasm (subst_trace (Val_Bool b) v es)) -∗
  WPasm (Smt (DeclareConst v Ty_Bool) ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
  Unshelve. exact true.
Qed.

Lemma wp_declare_const_bv' `{!islaG Σ} `{!threadG} v es ann b:
  (∀ (n : bv b), ▷WPasm (subst_trace (Val_Bits n) v es)) -∗
  WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by apply DeclareConstBitVecS'|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
  Unshelve. apply: inhabitant.
Qed.

Lemma wp_declare_const_enum' `{!islaG Σ} `{!threadG} v es i ann:
  (∀ c, ▷ WPasm (subst_trace (Val_Enum (c)) v es)) -∗
  WPasm (Smt (DeclareConst v (Ty_Enum i)) ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
  Unshelve. exact: inhabitant.
Qed.

Lemma wp_define_const' `{!islaG Σ} `{!threadG} n es ann e:
  WPexp e {{ v, ▷ WPasm (subst_trace v n es) }} -∗
  WPasm (Smt (DefineConst n e) ann :t: es).
Proof.
  rewrite wp_asm_unfold wp_exp_unfold. iDestruct 1 as (v Hv) "Hcont".
  rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
Qed.

Lemma wp_assert' `{!islaG Σ} `{!threadG} es ann e:
  WPexp e {{ v, (∃ b, ⌜v = Val_Bool b⌝ ∗ ▷ (⌜b = true⌝ -∗ WPasm es)) }} -∗
  WPasm (Smt (Assert e) ann :t: es).
Proof.
  rewrite wp_exp_unfold. iDestruct 1 as (v Hv b ?) "Hcont". subst v.
  rewrite !wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. destruct b.
    all: eexists _, _, _, _; econstructor; [done |by econstructor| done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  destruct b => /=; last by iApply wp_value.
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_branch' `{!islaG Σ} `{!threadG} c desc es ann:
  ▷ WPasm es -∗
  WPasm (Branch c desc ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
Qed.

Lemma wp_read_reg' `{!islaG Σ} `{!threadG} r v vread ann es al:
  read_accessor al v = Some vread →
  WPreadreg r @ al {{ v', ▷ (⌜vread = v'⌝ -∗ WPasm es) }} -∗
  WPasm (ReadReg r al v ann :t: es).
Proof.
  rewrite wp_asm_eq wpreadreg_eq. iIntros (?) "Hr".
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct ("Hr" with "Hθ") as (v' v'' ??) "[? Hcont]".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _, _, _. split_and! => //. by right.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[?[?[?[?[[??]|?]]]]]]]]]; simplify_eq/=. 2: {
    iFrame. iSplitL; [|done]. by iApply wp_value.
  }
  iFrame; iSplitL; [|done].
  iApply ("Hcont" with "[//]"); [done..|].
  iFrame.
Qed.

Lemma wp_write_reg_acc' `{!islaG Σ} `{!threadG} r v v' v'' vnew ann es al:
  read_accessor al v = Some vnew →
  write_accessor al v' vnew = Some v'' →
  r ↦ᵣ v' -∗
  ▷ (r ↦ᵣ v'' -∗ WPasm es) -∗
  WPasm (WriteReg r al v ann :t: es).
Proof.
  iIntros (? ?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _, _, _. done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
  unfold sail_name in *. simplify_eq.
  iFrame; iSplitL; [|done].
  iMod (reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]".
  iApply ("Hcont" with "Hr"); [done..|].
  iFrame.
Qed.

Lemma wp_write_reg_struct' `{!islaG Σ} `{!threadG} r v v' vnew ann es f:
  read_accessor [Field f] v = Some vnew →
  r # f ↦ᵣ v' -∗
  ▷ (r # f ↦ᵣ vnew -∗ WPasm es) -∗
  WPasm (WriteReg r [Field f] v ann :t: es).
Proof.
  iIntros (?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (struct_reg_mapsto_lookup with "Hθ Hr") as %(?&?&?&?&?).
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _, _, _. split_and! => //. rewrite /write_accessor/=. by simplify_option_eq.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
  unfold sail_name, write_accessor in *. simplify_option_eq.
  iFrame; iSplitL; [|done].
  iMod (struct_reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]"; [done..|].
  iApply ("Hcont" with "Hr"); [done..|].
  iFrame.
Qed.

Lemma wp_write_reg' `{!islaG Σ} `{!threadG} r v v' ann es:
  r ↦ᵣ v' -∗
  ▷ (r ↦ᵣ v -∗ WPasm es) -∗
  WPasm (WriteReg r [] v ann :t: es).
Proof. by apply: wp_write_reg_acc'. Qed.

Lemma wp_read_mem' `{!islaG Σ} `{!threadG} n len a vread (vmem : bv n) es ann kind tag q:
  n = (8 * len)%N →
  0 < Z.of_N len →
  bv_unsigned a ↦ₘ{q} vmem -∗
  ▷ (⌜vread = vmem⌝ -∗ bv_unsigned a ↦ₘ{q} vmem -∗ WPasm es) -∗
  WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
Proof.
  iIntros (??) "Hm Hcont". setoid_rewrite wp_asm_unfold. subst.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
  have ? : len' = len by lia. subst.
  iSplit. {
    iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |] => /=.
    eexists _, _, _. simplify_option_eq. naive_solver.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[?[??]]]]]];
    simplify_option_eq; destruct_and!; destruct_or!; destruct_and?; simplify_eq. 2:{
    iFrame. iSplitL; [|done]. by iApply wp_value.
  }
  iFrame. iSplit; [|done].
  iApply ("Hcont" with "[] [Hm]"); done.
Qed.

Lemma wp_write_mem' `{!islaG Σ} `{!threadG} n len a (vold vnew : bv n) es ann res kind tag:
  n = (8 * len)%N →
  0 < Z.of_N len →
  bv_unsigned a ↦ₘ vold -∗
  ▷ (bv_unsigned a ↦ₘ vnew -∗ WPasm es) -∗
  WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
Proof.
  iIntros (??) "Hm Hcont". subst. setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
  have ? : len' = len by lia. subst.
  iSplit. {
    iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |]. simpl.
    eexists _, _, _. simplify_option_eq. naive_solver.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_".
  inv_seq_step.
  revert select (∃ _, _) => -[?[?[?[?[??]]]]]; simplify_option_eq; destruct_and!; simplify_eq.
  iMod (mem_mapsto_update with "Hmem Hm") as (len' ?) "[Hmem Hm]".
  rewrite Z_to_bv_bv_unsigned. have ? : len' = len by lia. subst. iFrame.
  iModIntro. iSplitL; [|done].
  by iApply ("Hcont" with "Hm").
Qed.

Lemma wp_branch_address' `{!islaG Σ} `{!threadG} v es ann:
  ▷ WPasm es -∗
  WPasm (BranchAddress v ann :t: es).
Proof.
  iIntros "Hcont". setoid_rewrite wp_asm_unfold.
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    done.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplitL; [|done].
  iApply ("Hcont"); [done..|].
  iFrame.
Qed.

Lemma wp_barrier' `{!islaG Σ} `{!threadG} es v ann:
  ▷ WPasm es -∗
  WPasm (Barrier v ann :t: es).
Proof.
  rewrite wp_asm_eq.
  iIntros "Hcont" ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro.
    eexists _, _, _, _; econstructor; [done |by econstructor| done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_assume_reg' `{!islaG Σ} `{!threadG} r v ann es al:
  WPreadreg r @ al {{ v', ⌜v = v'⌝ ∗ ▷ WPasm es }} -∗
  WPasm (AssumeReg r al v ann :t: es).
Proof.
  rewrite wp_asm_eq wpreadreg_eq. iIntros "Hr".
  iIntros ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "(?&Hictx&?)".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iDestruct ("Hr" with "Hθ") as (v' v'' ??) "[Hr [% Hcont]]"; subst.
  iSplit. {
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
    eexists _. split_and! => //.
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[??]]]]]; simplify_eq/=.
  iFrame; iSplitL; [|done].
  iApply ("Hcont" with "[]"); [done..|].
  iFrame.
Qed.

Lemma wp_assume' `{!islaG Σ} `{!threadG} es ann e:
  WPaexp e {{ v, ⌜v = Val_Bool true⌝ ∗ ▷ WPasm es }} -∗
  WPasm (Assume e ann :t: es).
Proof.
  rewrite wp_a_exp_unfold wp_asm_eq.
  iIntros "Hexp" ([????]) "/= -> -> -> Hθ".
  iDestruct ("Hexp" with "Hθ") as (v ?) "(Hθ&%&Hcont)"; subst.
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro.
    eexists _, _, _, _; econstructor; [done | by econstructor|done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_abstract_primop' `{!islaG Σ} `{!threadG} es n v args ann:
  ▷ WPasm es -∗
  WPasm (AbstractPrimop n v args ann :t: es).
Proof.
  rewrite wp_asm_eq.
  iIntros "Hcont" ([????]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    iPureIntro.
    eexists _, _, _, _; econstructor; [done |by econstructor| done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
  inv_seq_step.
  iFrame; iSplit; [|done].
  iApply "Hcont"; [done..|iFrame].
Qed.

Lemma wp_cases' `{!islaG Σ} `{!threadG} ts:
  ts ≠ [] →
  ▷(∀ t, ⌜t ∈ ts⌝ -∗ WPasm t) -∗
  WPasm (tcases ts).
Proof.
  iIntros (?) "Hwp". setoid_rewrite wp_asm_unfold.
  iIntros ([? regs ? ?]) "/= -> -> -> Hθ".
  iApply lifting.wp_lift_step; [done|].
  iIntros (σ1 ??? ?) "Hctx".
  iApply fupd_mask_intro; first set_solver. iIntros "HE".
  iSplit. {
    destruct ts => //.
    iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |econstructor; by left|done].
  }
  iIntros "!>" (????) "_". iMod "HE" as "_".
  inv_seq_step. iModIntro.
  iFrame. iSplitL; [|done].
  by iApply "Hwp".
Qed.
