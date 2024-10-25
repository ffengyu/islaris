Require Import isla.riscv64.riscv64.

Context `{!islaG Σ} `{!threadG}.

Lemma zgtz : 0 > 0 -> False.
  lia.
Qed.

Definition pred_strong1 (n: nat): n > 0 -> nat :=
  match n with
  | O => fun pf => match zgtz pf with end
  | S n' => fun _ => n'
  end.

Theorem two_gt0 : 2 > 0.
  lia.
Qed.

Eval compute in pred_strong1 2 two_gt0.
