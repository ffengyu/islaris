From Coq Require Export ssreflect.
From stdpp Require Export prelude strings gmap.
From RecordUpdate Require Export RecordSet.
From iris.proofmode Require Import tactics.
From refinedc.lang Require Export base.
Require Export isla.bitvector.
Export RecordSetNotations.

Open Scope Z_scope.

Global Set Default Proof Using "Type".
Global Unset Program Cases.
Global Set Keyed Unification.
Global Set Default Goal Selector "!".

Arguments set _ _ _ _ _ !_ /.

Arguments N.mul : simpl never.
Arguments bool_decide : simpl never.
Typeclasses Opaque prefix.

Ltac unLET :=
  repeat match goal with
         | H := _ |- _ => unfold H in *; clear H
         end.
Tactic Notation "case_match" "as" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.

(* This has as better performance characteristic wrt. simpl compared
to list_find since list_find_idx does not contain prod_map. *)
Definition list_find_idx {A} P `{∀ x, Decision (P x)} : list A → option nat :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if decide (P x) then Some 0%nat else S <$> go l
  end.
Global Instance: Params (@list_find_idx) 3 := {}.

Section list_find_idx.
  Context {A} (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma list_find_idx_list_find l:
    list_find_idx P l = fst <$> list_find P l.
  Proof.
    elim: l => //= ?? ->. case_decide => //=.
    rewrite -!option_fmap_compose. by apply: option_fmap_ext.
  Qed.

  Lemma list_find_idx_Some l i:
    list_find_idx P l = Some i ↔
    ∃ x, l !! i = Some x ∧ P x ∧ ∀ j y, l !! j = Some y → (j < i)%nat → ¬P y.
  Proof.
    rewrite list_find_idx_list_find fmap_Some.
    split.
    - move => -[[??]]. rewrite list_find_Some. naive_solver.
    - move => [??]. eexists (_, _). rewrite list_find_Some. naive_solver.
  Qed.

  Lemma list_find_idx_lt l i:
    list_find_idx P l = Some i → (i < length l)%nat.
  Proof. move => /list_find_idx_Some[?[??]]. by apply: lookup_lt_Some. Qed.

  Lemma list_find_idx_insert_eq l i x:
    list_find_idx P l = Some i →
    P x →
    list_find_idx P (<[i:=x]> l) = Some i.
  Proof.
    rewrite !list_find_idx_Some => -[?[?[??]]] ?. eexists _.
    rewrite list_lookup_insert. 2: by apply: lookup_lt_Some. split_and! => //.
    move => ?? /list_lookup_insert_Some. naive_solver.
  Qed.

  Lemma list_find_idx_insert_neq l i j x y:
    list_find_idx P l = Some i →
    ¬ P x →
    l !! j = Some y →
    ¬ P y →
    list_find_idx P (<[j:=x]> l) = Some i.
  Proof.
    rewrite !list_find_idx_Some => -[?[?[??]]] ???. eexists _.
    rewrite list_lookup_insert_ne. 2: move => ?; by simplify_eq.
    split_and! => //. move => ?? /list_lookup_insert_Some. naive_solver.
  Qed.
End list_find_idx.

Section map_Forall.
  Context `{FinMap K M}.
  Context {A} (P : K → A → Prop).
  Implicit Types m : M A.

  Lemma map_Forall_impl' (Q : K → A → Prop) m :
    map_Forall P m → (∀ i x, m !! i = Some x → P i x → Q i x) → map_Forall Q m.
  Proof. unfold map_Forall; naive_solver. Qed.
  Lemma map_Forall_insert_2' m i x :
    P i x → map_Forall (λ j y, i ≠ j → P j y) m → map_Forall P (<[i:=x]>m).
  Proof using Type*. intros ?? j y; rewrite lookup_insert_Some; naive_solver. Qed.

End map_Forall.

From iris.bi Require Import bi.

Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Section sep_map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.
  Lemma big_sepM_kmap {B} `{Countable B} (f : K → B) (Φ : B → A → PROP) m `{!Inj eq eq f}:
    ([∗ map] k↦y ∈ kmap f m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ (f k) y).
  Proof.
    induction m as [|???? IH] using map_ind => /=. { by rewrite kmap_empty !big_sepM_empty. }
    rewrite kmap_insert !big_sepM_insert // ?IH // lookup_kmap_None => ??. by simplify_eq.
  Qed.

  Lemma big_sepM_list_to_map (Φ : K → A → PROP) l:
    NoDup l.*1 →
    ([∗ map] k↦y ∈ list_to_map l, Φ k y) ⊣⊢ ([∗ list] y ∈ l, Φ y.1 y.2).
  Proof.
    induction l as [|?? IH]; csimpl. { by rewrite !big_sepM_empty. }
    move => /NoDup_cons[??]. rewrite big_sepM_insert ?IH //.
    by apply: not_elem_of_list_to_map_1.
  Qed.
End sep_map.
End big_op.


Lemma big_sepL_exist {PROP : bi} {A B} (l : list A) (Φ : _ → _ → _ → PROP) `{!BiAffine PROP} :
  ([∗ list] i↦x∈l, ∃ y : B, Φ i x y) -∗
   ∃ xs : list B, ⌜length xs = length l⌝ ∗ ([∗ list] i↦x∈l, ∃ y : B, ⌜xs !! i = Some y⌝ ∗ Φ i x y).
Proof.
  iIntros "Hl".
  iInduction (l) as [|? l] "IH" forall (Φ).
  { iExists []. iSplit; done. }
  simpl. iDestruct "Hl" as "[[%x Hx] Hl]".
  iDestruct ("IH" with "Hl") as (xs) "[%Heq ?]".
  iExists (x::xs) => /=. iSplit; [by rewrite /= Heq|]. iFrame.
  iExists _. by iFrame.
Qed.

(** fixpoints based on iris/bi/lib/fixpoint.v *)
Class MonoPred {A : Type} (F : (A → Prop) → (A → Prop)) := {
  mono_pred (Φ Ψ : _ → Prop) :
    (∀ x, Φ x → Ψ x) → ∀ x, F Φ x → F Ψ x;
}.
Global Arguments mono_pred {_ _ _} _ _.

Definition least_fixpoint {A : Type}
    (F : (A → Prop) → (A → Prop)) (x : A) : Prop :=
  tc_opaque (∀ Φ : A -> Prop, (∀ x, F Φ x → Φ x) → Φ x).
Global Arguments least_fixpoint : simpl never.
Definition greatest_fixpoint {A : Type}
    (F : (A → Prop) → (A → Prop)) (x : A) : Prop :=
  tc_opaque (∃ Φ : A -> Prop, (∀ x, Φ x → F Φ x) ∧ Φ x).
Global Arguments greatest_fixpoint : simpl never.

Section least.
  Context {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}.

  Lemma least_fixpoint_unfold_2 x : F (least_fixpoint F) x → least_fixpoint F x.
  Proof using Type*.
    rewrite /least_fixpoint /=. move => HF Φ Hincl.
    apply Hincl. apply: mono_pred; [|done].
    move => /= y Hy. apply Hy. done.
  Qed.

  Lemma least_fixpoint_unfold_1 x : least_fixpoint F x → F (least_fixpoint F) x.
  Proof using Type*.
    move => HF. apply HF. move => y Hy /=. apply: mono_pred; [|done].
    move => z Hz. by apply: least_fixpoint_unfold_2.
  Qed.

  Lemma least_fixpoint_unfold x : least_fixpoint F x ↔ F (least_fixpoint F) x.
  Proof using Type*. split; eauto using least_fixpoint_unfold_1, least_fixpoint_unfold_2. Qed.

  Lemma least_fixpoint_ind (Φ : A → Prop) :
    (∀ y, F Φ y → Φ y) → ∀ x, least_fixpoint F x → Φ x.
  Proof. move => HΦ x HF. by apply: HF. Qed.
End least.

Section greatest.
  Context {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}.

  Lemma greatest_fixpoint_unfold_1 x :
    greatest_fixpoint F x → F (greatest_fixpoint F) x.
  Proof using Type*.
    move => [Φ [Hincl HΦ]].
    apply: (mono_pred Φ); [| by apply: Hincl].
    move => y Hy. eexists Φ. naive_solver.
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (greatest_fixpoint F) x → greatest_fixpoint F x.
  Proof using Type*.
    move => HF. eexists (F (greatest_fixpoint F)). split; [|done].
    move => y Hy. apply: mono_pred; [|done]. move => z. apply: greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    greatest_fixpoint F x ↔ F (greatest_fixpoint F) x.
  Proof using Type*.
    split; auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → Prop) :
    (∀ y, Φ y → F Φ y) → ∀ x, Φ x → greatest_fixpoint F x.
  Proof. move => HΦ x Hx. eexists Φ. naive_solver. Qed.
End greatest.
