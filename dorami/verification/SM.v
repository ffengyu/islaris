From isla.dorami Require Import model.
From isla.dorami Require Import transitions.

Section SM.

Context `{!islaG Σ} `{!threadG}.

(* Default value of csr/gpr, for example all zeros, represents the info that *)
(* do not contain any useful information. *)
Variable csr0 : list (bv 64).
Variable gpr0 : list (bv 64).
(* The addr before the instruction to return to Enclave. *)
Variable ret_Encl_addr : bv 64.

Hypothesis csr0_length : length csr0 = 4%nat.
Hypothesis gpr0_length : length gpr0 = 5%nat.

(* F only sees the mcause passed from Enclave. All the other information *)
(* F sees is the default values csr0 and gpr0. *)
Definition E2F_spec (mcause: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)) : iProp Σ :=
  P P_mtvec P_pmpcfgs (<[2%nat := mcause]> csr) gpr mem ∗
  instr_pre (bv_unsigned P2F_code_addr) (
    ∃ mem', P P_mtvec P_pmpcfgs (<[2%nat := mcause]> csr0) gpr0 mem'
  ).

Arguments E2F_spec /.

(* Enclave only sees the x10 passed from F. Other the other information *)
(* Enclave sees is the default values csr0 and gpr0. *)
Definition F2E_spec (x10: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)): iProp Σ :=
  P P_mtvec P_pmpcfgs csr (<[3%nat := x10]> gpr) mem ∗
  instr_pre (bv_unsigned ret_Encl_addr) (
    ∃ mem', P P_mtvec P_pmpcfgs csr0 (<[3%nat := x10]> gpr0) mem'
  ).

Arguments F2E_spec /.

(* P_mtvec represents the first instruction after the transition from *)
(* Enclave to P. *)
Hypothesis E2F : ∀ (mcause: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)), ⊢ instr_body (bv_unsigned P_mtvec) (E2F_spec mcause csr gpr mem).

Hypothesis F2E : ∀ (x10: bv 64) (csr gpr: list (bv 64)) (mem: bv (0x20000 * 8)), ⊢ instr_body (bv_unsigned P_code_addr + P_entry_code_size) (F2E_spec x10 csr gpr mem).

(* The state justing leaving the enclave and entering P. *)
Definition leave_Encl mcause csr gpr Pmem Fmem :=
  Machine P_mtvec P_pmpcfgs (<[2%nat := mcause]> csr) gpr Pmem Fmem.

Arguments leave_Encl /.

(* The state just entering F from P *)
Definition start_F mcause Pmem Fmem :=
  Machine F_mtvec F_pmpcfgs (<[2%nat := mcause]> csr0) (<[2%nat := (BV 64 0x989B989D981E)]> gpr0) Pmem Fmem.

Arguments start_F /.

(* The state justing leaving F and entering P. *)
Definition leave_F x10 csr gpr Pmem Fmem :=
  Machine F_mtvec SP_pmpcfgs csr (<[3%nat := x10]> gpr) Pmem Fmem.

Arguments leave_F /.

(* The state entering Enclave in the next instruciton *)
Definition ret_Encl x10 Pmem Fmem :=
  Machine P_mtvec P_pmpcfgs csr0 (<[3%nat := x10]> gpr0) Pmem Fmem.

Arguments ret_Encl /.

(* This theorem shows that no matter what information enclave pass to P *)
(* and how P use this secret, the only thing F can see is the mcause *)
(* except the default values. *)
Theorem confidentiality :
  ∀ (mcause: bv 64) (csr gpr: list (bv 64)) (Pmem: bv (0x20000 * 8)) (Fmem: bv (0x1000 * 8)),
  length csr = 4%nat ->
  length gpr = 5%nat ->
  (∃ v, csr !! 0%nat = Some v ∧ (bv_extract 3 1 v) = (BV 1 0x0)) ->
  ⊢
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
  instr_body (bv_unsigned P_mtvec) (
    Machine P_mtvec P_pmpcfgs (<[2%nat := mcause]> csr) gpr Pmem Fmem ∗
    instr_pre (bv_unsigned F_code_addr)
      (∃ Pmem', Machine F_mtvec F_pmpcfgs (<[2%nat := mcause]> csr0) (<[2%nat := (BV 64 0x989B989D981E)]> gpr0) Pmem' Fmem)
  ).
Proof using E2F H csr0 csr0_length gpr0 gpr0_length ret_Encl_addr.
  intros mcause csr gpr Pmem Fmem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try inversion Hcsr).
  do 6 (destruct gpr as [|? gpr]; try inversion Hgpr).
  destruct csr0 as [|? csr0'] eqn:Hcsr0 ; try inversion csr0_length.
  destruct gpr0 as [|? gpr0'] eqn:Hgpr0 ; try inversion gpr0_length.
  do 4 (destruct csr0' as [|? csr0']; try inversion csr0_length).
  do 5 (destruct gpr0' as [|? gpr0']; try inversion gpr0_length).
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hcsr Hgpr.
  intros [ms [[= <-] Hms]].
  iStartProof.
  iPoseProof (E2F mcause [b; b0; mcause; b2] [b3; b4; b5; b6; b7] Pmem) as "HE2F".
  liARun.
  rewrite Hcsr0 Hgpr0.
  iPoseProof (P2F [b8; b10; mcause; b12] [b9; b13; b14; b15; b16] Pmem with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "HP2F"; try done.
  liSimpl.
  liARun.
  iFrame.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

(* This theorem shows that no matter what information F pass to P *)
(* and how P use this secret, the only thing Encl can see is the x10 *)
(* except the default values and it will finally returns to Enclave *)
(* directly without nesting call of F. *)
Theorem integrity :
  ∀ (x10: bv 64) (csr gpr: list (bv 64)) Pmem Fmem,
  length csr = 4%nat ->
  length gpr = 5%nat ->
  ⊢
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
  instr (bv_unsigned P_code_addr) (Some P_entry.a0.a0) -∗
  instr (bv_unsigned P_code_addr + 0x4) (Some P_entry.a4.a4) -∗
  instr (bv_unsigned P_code_addr + 0x8) (Some P_entry.a8.a8) -∗
  instr (bv_unsigned P_code_addr + 0xc) (Some P_entry.ac.ac) -∗
  instr (bv_unsigned P_code_addr + 0x10) (Some P_entry.a10.a10) -∗
  instr (bv_unsigned P_code_addr + 0x14) (Some P_entry.a14.a14) -∗
  instr (bv_unsigned P_code_addr + 0x18) (Some P_entry.a18.a18) -∗
  (∃ ins, instr ((bv_unsigned P_code_addr + 0x1c)) (Some ins)) -∗
  instr_body (bv_unsigned SP_code_addr) (
    Machine F_mtvec SP_pmpcfgs csr (<[3%nat := x10]> gpr) Pmem Fmem ∗
    instr_pre (bv_unsigned ret_Encl_addr)
      (∃ Pmem', Machine P_mtvec P_pmpcfgs csr0 (<[3%nat := x10]> gpr0) Pmem' Fmem)
  ).
Proof using F2E H csr0 csr0_length gpr0 gpr0_length ret_Encl_addr.
  intros x10 csr gpr Pmem Fmem Hcsr Hgpr.
  do 5 (destruct csr as [|? csr]; try inversion Hcsr).
  do 6 (destruct gpr as [|? gpr]; try inversion Hgpr).
  destruct csr0 as [|? csr0'] eqn:Hcsr0 ; try inversion csr0_length.
  destruct gpr0 as [|? gpr0'] eqn:Hgpr0 ; try inversion gpr0_length.
  do 4 (destruct csr0' as [|? csr0']; try inversion csr0_length).
  do 5 (destruct gpr0' as [|? gpr0']; try inversion gpr0_length).
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hcsr Hgpr.
  iStartProof.
  iIntros "? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hret".
  iPoseProof (SP2P_entry [b; b0; b1; b2] [b3; b4; b5; x10; b7] with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "HP2P_entry"; try done.
  liARun.
  iPoseProof (F2E x10 [ms; b0; b1; b2] [b3; b4; LET9; x10; b7] Pmem) as "HF2E".
  liARun.
  rewrite Hcsr0.
  liARun.
  iExists (mem', ())ₗ.
  liARun.
  rewrite Hgpr0.
  liARun.
  iFrame.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

End SM.
