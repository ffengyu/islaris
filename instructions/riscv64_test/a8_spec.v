Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.riscv64_test.a8.

Lemma a8_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a8)
  ⊢ instr_body pc (sd_spec pc "x11" "x2" (8)).
Proof.
  iStartProof.
  do 30 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  do 10 liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  simple notypeclasses refine (tac_li_tactic _ _ _ _ _).
  1:{
  clear;
  autounfold with regcol_compute_unfold;
  repeat match goal with | H := _ |- _  => clearbody H end.
  remember_regcol.
  lazymatch goal with
  | |- LiTactic (regcol_compute_hint ?f ?a) =>
      (* We first compute the result of f a such that we don't need to
      create an evor for it, but can use [abstract]. This is important
      since the [clearbody]s above are otherwise ignored at Qed time,
      leading to divergence of vm_compute. This means that we run
      vm_compute twice, but it should be fast anyway. *)
      let x := eval vm_compute in (f a) in
      idtac x
  end.
  lazymatch goal with
  | |- LiTactic (regcol_compute_hint ?f ?a) =>
      (* We first compute the result of f a such that we don't need to
      create an evor for it, but can use [abstract]. This is important
      since the [clearbody]s above are otherwise ignored at Qed time,
      leading to divergence of vm_compute. This means that we run
      vm_compute twice, but it should be fast anyway. *)
      let x := eval vm_compute in (f a) in
      lazymatch x with
      | Some ?y => apply (regcol_compute_hint_hint y)
      end
  end.
  abstract (vm_compute; exact eq_refl).
  }

  liTactic.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a8_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a8_spec pc).
Global Existing Instance a8_spec_inst.
