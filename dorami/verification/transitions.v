From isla.dorami Require Import model.

(* This frame rule is the base of the following separated proof. *)
(* Without this frame rule, we cannot compose them together. *)
(* This rule doesn't necessarily hold because they are not equiv to *)
(* weakest precondition. *)
(* As we show in F_universal_contract, instr_pre has less expressiveness *)
(* power than weeakestpre in safety but instr_pre can express not only *)
(* safety. *)
Lemma instrpre_frame `{!islaG Σ} `{!threadG} (start_addr end_addr: bv 64) (P Q R: iProp Σ) :
  instr_body (bv_unsigned start_addr) (P ∗ instr_pre (bv_unsigned end_addr) Q) ⊢
  instr_body (bv_unsigned start_addr) (P ∗ R ∗ instr_pre (bv_unsigned end_addr) (Q ∗ R)).
Proof.
  iIntros "Hpre".
  iApply (instr_pre_wand with "Hpre"); try done.
  iIntros "(?&?&Hpre)"; iFrame.
  iApply (instr_pre_wand with "Hpre"); try done.
  by iIntros; iFrame.
Qed.

(* The specification of transition from P to F *)
Definition P2F_spec `{!islaG Σ} `{!threadG} (csr gpr: list (bv 64)) (mem: (bv (0x20000 * 8))) : iProp Σ :=
  P P_mtvec P_pmpcfgs csr gpr mem ∗
  instr_pre (bv_unsigned F_code_addr) (
    P F_mtvec F_pmpcfgs csr (<[2%nat := (BV 64 0x989B989D981E)]>gpr) mem ∗
    True
  ).

Arguments P2F_spec /.

Theorem P2F `{!islaG Σ} `{!threadG} :
  ∀ csr gpr mem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned F_code_addr - 0x2c) (Some P2F.a0.a0) -∗
  instr (bv_unsigned F_code_addr - 0x28) (Some P2F.a4.a4) -∗
  instr (bv_unsigned F_code_addr - 0x24) (Some P2F.a8.a8) -∗
  instr (bv_unsigned F_code_addr - 0x20) (Some P2F.ac.ac) -∗
  instr (bv_unsigned F_code_addr - 0x1c) (Some P2F.a10.a10) -∗
  instr (bv_unsigned F_code_addr - 0x18) (Some P2F.a14.a14) -∗
  instr (bv_unsigned F_code_addr - 0x14) (Some P2F.a18.a18) -∗
  instr (bv_unsigned F_code_addr - 0x10) (Some P2F.a1c.a1c) -∗
  instr (bv_unsigned F_code_addr - 0xc) (Some P2F.a20.a20) -∗
  instr (bv_unsigned F_code_addr - 0x8) (Some P2F.a24.a24) -∗
  instr (bv_unsigned F_code_addr - 0x4) (Some P2F.a28.a28) -∗
  instr_body (bv_unsigned F_code_addr - 0x2c) (P2F_spec csr gpr mem).
Proof.
  intros csr gpr mem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

(* The specification of transition from SallyPort to P_entry *)
Definition SP_spec `{!islaG Σ} `{!threadG} (csr gpr: list (bv 64)) : iProp Σ :=
  SP F_mtvec SP_pmpcfgs true csr gpr ∗
  instr_pre (bv_unsigned P_code_addr) (
    ∃ ms, SP P_mtvec P_entry_pmpcfgs false (ms::(tl csr)) (<[2%nat := (BV 64 0x9B989D989D1E)]>gpr) ∗
    True
  ).

Arguments SP_spec /.

(* We have to prove this specification of instruction a0 separately *)
(* because this has many branches and interrupt is disabled after it. *)
Definition SP_a0_spec `{!islaG Σ} `{!threadG}  (csr gpr: list (bv 64)) : iProp Σ :=
  SP F_mtvec SP_pmpcfgs true csr gpr ∗
  instr_pre (bv_unsigned SP_code_addr + 4) (
    ∃ ms,
    SP F_mtvec SP_pmpcfgs false (<[0%nat := ms]> csr) gpr
  ).

Arguments SP_a0_spec /.

Theorem SP_a0 `{!islaG Σ} `{!threadG} :
  ∀ csr gpr,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned SP_code_addr) (Some Sally_Port.a0.a0)
  ⊢ instr_body (bv_unsigned SP_code_addr) (SP_a0_spec csr gpr).
Proof.
  intros csr gpr Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  do 28 liAStep.
  iIntros "(Hcsr&?&?)".
  iPoseProof (reg_col_lookup _ 0 with "Hcsr") as "(%v&%Hv&Hms&Hcsr) "; first done.
  rewrite /valu_has_shape /= in Hv.
  destruct v; first [done | destruct Hv as [Hlen Hv]].
  do 2 (destruct l; try done).
  destruct p.
  destruct Hv as [[Hp1 Hp2] _].
  simpl in Hp1, Hp2 |- *.
  rewrite -Hp1 Hp2.
  liARun.
  (* TODO: automate it *)
  (* Here we change the automation to read/write the field in struct reg. *)
  (* But the support is not complete. *)
  repeat (iApply find_in_context_reg_mapstostruct; iExists 0%nat; liARun).
  all: iRevert select ("mstatus" ↦ᵣ _)%I.
  all: match goal with
      | |- environments.envs_entails _ (("mstatus" ↦ᵣ RegVal_Struct [("bits", RVal_Bits (bv_to_bvn ?ms))])-∗ _) =>
          iIntros; iExists (ms, ())ₗ
      end.
  all: liARun; iFrame.
  Unshelve.
  all: prepare_sidecond.
  all: bv_simplify; bitblast.
Qed.

Theorem SP2P_entry `{!islaG Σ} `{!threadG} :
  ∀ csr gpr,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned SP_code_addr) (Some Sally_Port.a0.a0) -∗
  instr (bv_unsigned SP_code_addr + 0x4) (Some Sally_Port.a4.a4) -∗
  instr (bv_unsigned SP_code_addr + 0x8) (Some Sally_Port.a8.a8) -∗
  instr (bv_unsigned SP_code_addr + 0xc) (Some Sally_Port.ac.ac) -∗
  instr (bv_unsigned SP_code_addr + 0x10) (Some Sally_Port.a10.a10) -∗
  instr (bv_unsigned SP_code_addr + 0x14) (Some Sally_Port.a14.a14) -∗
  instr (bv_unsigned SP_code_addr + 0x18) (Some Sally_Port.a18.a18) -∗
  instr (bv_unsigned SP_code_addr + 0x1c) (Some Sally_Port.a1c.a1c) -∗
  instr (bv_unsigned SP_code_addr + 0x20) (Some Sally_Port.a20.a20) -∗
  instr (bv_unsigned SP_code_addr + 0x24) (Some Sally_Port.a24.a24) -∗
  instr (bv_unsigned SP_code_addr + 0x28) (Some Sally_Port.a28.a28) -∗
  instr (bv_unsigned SP_code_addr + 0x2c) (Some Sally_Port.a2c.a2c) -∗
  instr_body (bv_unsigned SP_code_addr) (SP_spec csr gpr).
Proof.
  intros csr gpr Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  iIntros.
  iPoseProof (SP_a0 [b; b0; b1; b2] [b3; b4; b5; b6; b7] with "[$]") as "Ha0_spec"; try done.
  liARun.
  iExists (ms, ())ₗ.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

(* The specification of transition from P_entry to P *)
Definition P_entry2P_spec `{!islaG Σ} `{!threadG} (csr gpr csr' gpr': list (bv 64)) (mem: (bv (0x20000 * 8))) :iProp Σ :=
  P P_mtvec P_entry_pmpcfgs csr gpr mem ∗
  instr_pre (bv_unsigned P_code_addr + 0x1c) (
    P P_mtvec P_pmpcfgs csr (<[2%nat := (BV 64 0x9B9898989D1E)]>gpr) mem ∗
    True
  ).

Arguments P_entry2P_spec /.

Lemma P_entry2P `{!islaG Σ} `{!threadG} :
  ∀ csr gpr mem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  instr (bv_unsigned P_code_addr) (Some P_entry.a0.a0) -∗
  instr (bv_unsigned P_code_addr + 0x4) (Some P_entry.a4.a4) -∗
  instr (bv_unsigned P_code_addr + 0x8) (Some P_entry.a8.a8) -∗
  instr (bv_unsigned P_code_addr + 0xc) (Some P_entry.ac.ac) -∗
  instr (bv_unsigned P_code_addr + 0x10) (Some P_entry.a10.a10) -∗
  instr (bv_unsigned P_code_addr + 0x14) (Some P_entry.a14.a14) -∗
  instr (bv_unsigned P_code_addr + 0x18) (Some P_entry.a18.a18) -∗
  instr_body (bv_unsigned P_code_addr) (P_entry2P_spec csr gpr csr (<[2%nat := (BV 64 0x9B9898989D1E)]>gpr) mem).
Proof.
  intros csr gpr mem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try done).
  do 6 (destruct gpr as [|? gpr]; try done).
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.
