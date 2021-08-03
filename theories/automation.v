From iris.proofmode Require Import coq_tactics reduction.
From refinedc.lithium Require Export lithium tactics.
From isla Require Export lifting bitvector_auto.
Set Default Proof Using "Type".

(** * Simplification and normalization hints *)
Global Instance simpl_val_bits_bv_to_bvn n (b1 b2 : bv n) :
  SimplBoth (Val_Bits b1 = Val_Bits b2) (b1 = b2).
Proof. split; naive_solver. Qed.

Lemma ite_bits n b (n1 n2 : bv n) :
  ite b (Val_Bits n1) (Val_Bits n2) = Val_Bits (ite b n1 n2).
Proof. by destruct b. Qed.
Hint Rewrite ite_bits : lithium_rewrite.

Hint Rewrite Z_to_bv_checked_bv_unsigned : lithium_rewrite.

(** * Registering extensions *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac normalize_tac ::= normalize_autorewrite.

Definition let_bind_hint {A B} (x : A) (f : A → B) : B :=
  f x.

Inductive instr_kind {Σ} : Type :=
| IKInstr (ins : option (list trc)) | IKPre (l : bool) (P : iProp Σ).
Definition FindInstrKind {Σ} `{!islaG Σ} `{!threadG} (a : Z) := {| fic_A := @instr_kind Σ; fic_Prop ik :=
  match ik with
  | IKInstr ins => instr a ins
  | IKPre l P => instr_pre' l a P
  end
|}.
Typeclasses Opaque FindInstrKind.

Section instances.
  Context `{!islaG Σ} `{!threadG}.

  Global Instance instr_intro_pers i a : IntroPersistent (instr a i) (instr a i).
  Proof. constructor. iIntros "#$". Qed.

  Lemma find_in_context_instr_kind_pre a T:
    (∃ l P, instr_pre' l a P ∗ T (IKPre l P)) -∗
    find_in_context (FindInstrKind a) T.
  Proof. iDestruct 1 as (??) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_instr_kind_pre_inst a :
    FindInContext (FindInstrKind a) 0%nat FICSyntactic :=
    λ T, i2p (find_in_context_instr_kind_pre a T).

  Lemma find_in_context_instr_kind_instr a T:
    (∃ ins, instr a ins ∗ T (IKInstr ins)) -∗
    find_in_context (FindInstrKind a) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_instr_kind_instr_inst a :
    FindInContext (FindInstrKind a) 1%nat FICSyntactic :=
    λ T, i2p (find_in_context_instr_kind_instr a T).
  Definition FindMapsto `{!islaG Σ} (a : addr) (n : N) := {|
    fic_A := bv n; fic_Prop v := a ↦ₘ v;
  |}%I.

  Global Instance mem_related `{!islaG Σ} a n (v : bv n) : RelatedTo (a ↦ₘ v) := {|
    rt_fic := FindMapsto a n;
  |}.

  Lemma find_in_context_mapsto_id `{!islaG Σ} a n T:
    (∃ v : bv n, a ↦ₘ v ∗ T v) -∗
    find_in_context (FindMapsto a n) T.
  Proof. iDestruct 1 as (v) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_mapsto_id_inst `{!islaG Σ} a n :
    FindInContext (FindMapsto a n) 0%nat FICSyntactic :=
    λ T, i2p (find_in_context_mapsto_id a n T).

  Inductive FICMapstoSemantic : Set :=.
  Global Instance find_in_context_mapsto_semantic_inst `{!islaG Σ} a n :
    FindInContext (FindMapsto a n) 1%nat FICMapstoSemantic :=
    λ T, i2p (find_in_context_mapsto_id a n T).

  Lemma tac_mapsto_eq `{!islaG Σ} l1 n (v1 v2 : bv n) l2:
    l1 = l2 →
    FindHypEqual FICMapstoSemantic (l1 ↦ₘ v1) (l2 ↦ₘ v2) (l1 ↦ₘ v2).
  Proof. by move => ->. Qed.

  Global Instance reg_related r v : RelatedTo (r ↦ᵣ v) := {|
    rt_fic := FindDirect (λ v, r ↦ᵣ v)%I;
  |}.

  Global Instance instr_related a i : RelatedTo (instr a i) := {|
    rt_fic := FindDirect (λ i, instr a i)%I;
  |}.

  Global Instance spec_trace_related κs : RelatedTo (spec_trace κs) := {|
    rt_fic := FindDirect (λ κs, spec_trace κs)%I;
  |}.

  Lemma subsume_reg r v1 v2 G:
    ⌜v1 = v2⌝ ∗ G -∗
    subsume (r ↦ᵣ v1) (r ↦ᵣ v2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_reg_inst r v1 v2 :
    Subsume (r ↦ᵣ v1) (r ↦ᵣ v2) :=
    λ G, i2p (subsume_reg r v1 v2 G).

  Lemma subsume_instr a i1 i2 G:
    ⌜i1 = i2⌝ ∗ G -∗
    subsume (instr a i1) (instr a i2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_instr_inst a i1 i2 :
    Subsume (instr a i1) (instr a i2) :=
    λ G, i2p (subsume_instr a i1 i2 G).

  Lemma subsume_spec_trace κs1 κs2 G:
    ⌜κs1 = κs2⌝ ∗ G -∗
    subsume (spec_trace κs1) (spec_trace κs2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_spec_trace_inst κs1 κs2 :
    Subsume (spec_trace κs1) (spec_trace κs2) :=
    λ G, i2p (subsume_spec_trace κs1 κs2 G).

  Lemma subsume_mem `{!islaG Σ} a n (v1 v2 : bv n) G:
    ⌜v1 = v2⌝ ∗ G -∗
    subsume (a ↦ₘ v1) (a ↦ₘ v2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_mem_inst  `{!islaG Σ} a n (v1 v2 : bv n) :
    Subsume (a ↦ₘ v1) (a ↦ₘ v2) :=
    λ G, i2p (subsume_mem a n v1 v2 G).

  Lemma li_wp_next_instr:
    (∃ (nPC : addr) bPC_changed,
        "_PC" ↦ᵣ Val_Bits nPC ∗ "__PC_changed" ↦ᵣ Val_Bool bPC_changed ∗
     ∃ a newPC,
       ⌜a = (if bPC_changed : bool then (bv_unsigned nPC) else (bv_unsigned nPC + instruction_size)%Z)⌝ ∗
       ⌜Z_to_bv_checked 64 a = Some newPC⌝ ∗
     find_in_context (FindInstrKind a) (λ ik,
     match ik with
     | IKInstr (Some ts) =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, "_PC" ↦ᵣ Val_Bits newPC -∗ "__PC_changed" ↦ᵣ Val_Bool false -∗ WPasm t
     | IKInstr (None) =>
       ∃ κs, spec_trace κs ∗ ⌜hd_error κs = Some (SInstrTrap newPC)⌝ ∗ True
     | IKPre l P => P
     end
    )) -∗
    WPasm [].
  Proof.
    iDestruct 1 as (??) "(HPC&Hchanged&Hwp)".
    iDestruct "Hwp" as (???? ins) "[Hi Hwp]". subst.
    destruct ins as [[?|]|?] => /=.
    - iDestruct "Hwp" as (?) "Hl".
      iApply (wp_next_instr with "[HPC Hchanged] Hi [Hl]") => //.
      + iExists _, _, _. by iFrame.
      + iIntros "!>" (i Hi) "? ?".
        iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
        iApply ("Hwp" with "[$] [$]").
    - iDestruct "Hwp" as (?) "(?&%&?)".
      iApply (wp_next_instr_extern with "[HPC Hchanged] [$] [$]") => //.
      iExists _, _, _. by iFrame.
    - iApply (wp_next_instr_pre with "[$] [HPC Hchanged] [$]").
      iExists _, _, _. by iFrame.
  Qed.

  Lemma li_instr_pre l a P:
    (∃ newPC, ⌜Z_to_bv_checked 64 a = Some newPC⌝ ∗
     find_in_context (FindInstrKind a) (λ ik,
     match ik with
     | IKInstr (Some ts) =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, P -∗ "_PC" ↦ᵣ Val_Bits newPC -∗ "__PC_changed" ↦ᵣ Val_Bool false -∗ WPasm t
     | IKInstr None =>
       P -∗ ∃ κs, spec_trace κs ∗ ⌜hd_error κs = Some (SInstrTrap newPC)⌝ ∗ True
     | IKPre l' Q => ⌜implb l' l⌝ ∗ (P -∗ Q)
     end
    )) -∗
    instr_pre' l a P.
  Proof.
    iDestruct 1 as (?? ins) "[Hinstr Hwp]".
    destruct ins as [[?|]|?] => /=.
    - iDestruct "Hwp" as (?) "Hl".
      iApply (instr_pre_intro_Some with "[$]"); [done..|].
      iIntros (i Hi) "???".
      iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
      iApply ("Hwp" with "[$] [$] [$]").
    - iApply (instr_pre_intro_None with "[$]"); [done..|].
      iIntros "HP".
      iDestruct ("Hwp" with "HP") as (?) "[? [% _]]".
      iExists _. by iFrame.
    - iDestruct "Hwp" as (?) "Hwand".
      by iApply (instr_pre_wand with "Hinstr").
  Qed.

  Lemma li_wp_read_reg r v ann es al:
    (∃ v' v'' vread, r ↦ᵣ v' ∗ ⌜read_accessor al v' = Some v''⌝ ∗
        ⌜read_accessor al v = Some vread⌝ ∗
       (⌜vread = v''⌝ -∗ r ↦ᵣ v' -∗ WPasm es)) -∗
    WPasm (ReadReg r al v ann :: es).
  Proof. iDestruct 1 as (???) "[Hr [% [% Hwp]]]". by iApply (wp_read_reg_acc with "Hr"). Qed.

  Lemma li_wp_write_reg r al v ann es:
    (∃ v' v'' vnew, r ↦ᵣ v' ∗
     ⌜read_accessor al v = Some vnew⌝ ∗ ⌜write_accessor al v' vnew = Some v''⌝ ∗
     (r ↦ᵣ v'' -∗ WPasm es)) -∗
    WPasm (WriteReg r al v ann :: es).
  Proof.
    iDestruct 1 as (???) "[Hr [% [% Hwp]]]"; simplify_eq/=.
      by iApply (wp_write_reg_acc with "Hr").
  Qed.

  Lemma li_wp_branch_address v ann es:
    WPasm es -∗
    WPasm (BranchAddress v ann :: es).
  Proof. apply: wp_branch_address. Qed.

  Lemma li_wp_declare_const_bv v es ann b:
    (∀ (n : bv b), WPasm ((subst_event v (Val_Bits n)) <$> es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :: es).
  Proof. apply: wp_declare_const_bv. Qed.

  Lemma li_wp_declare_const_bool v es ann:
    (∀ b : bool, WPasm ((subst_event v (Val_Bool b)) <$> es)) -∗
    WPasm (Smt (DeclareConst v Ty_Bool) ann :: es).
  Proof. apply: wp_declare_const_bool. Qed.

  Lemma li_wp_define_const n es ann e:
    WPexp e {{ v, let_bind_hint v (λ v, WPasm ((subst_event n v) <$> es)) }} -∗
    WPasm (Smt (DefineConst n e) ann :: es).
  Proof.
    iIntros "Hexp". iApply wp_define_const. unfold let_bind_hint.
    iApply (wpe_wand with "Hexp"). iIntros (?) "$".
  Qed.

  Lemma li_wp_assert es ann e:
    WPexp e {{ v, ∃ b, ⌜v = Val_Bool b⌝ ∗ (⌜b = true⌝ -∗ WPasm es) }} -∗
    WPasm (Smt (Assert e) ann :: es).
  Proof. apply: wp_assert. Qed.

  Lemma li_wp_write_mem len n success kind a (vnew : bv n) tag ann es:
    (∃ (vold : bv n),
    ⌜n = (8*len)%N⌝ ∗
    a ↦ₘ vold ∗
    (⌜success = true ⌝ -∗ a ↦ₘ vnew -∗ WPasm es)) -∗
    WPasm (WriteMem (Val_Bool success) kind (Val_Bits (BVN 64 a)) (Val_Bits (BVN n vnew)) len tag ann :: es).
  Proof. iDestruct 1 as (?) "[% [Hvold Hcont]]". by iApply (wp_write_mem with "Hvold Hcont"). Qed.

  Lemma li_wp_read_mem len n kind a vread tag ann es:
    (∃ vmem,
    ⌜n = (8 * len)%N⌝ ∗
    a ↦ₘ vmem ∗
    (⌜vread = vmem⌝ -∗ a ↦ₘ vmem -∗ WPasm es)) -∗
    WPasm (ReadMem (Val_Bits (BVN n vread)) kind (Val_Bits (BVN 64 a)) len tag ann :: es).
  Proof. iDestruct 1 as (?) "[% [Hmem Hcont]]". by iApply (wp_read_mem with "Hmem Hcont"). Qed.

  Lemma li_wpe_val v Φ ann:
    Φ v -∗
    WPexp (Val v ann) {{ Φ }}.
  Proof. apply: wpe_val. Qed.

  Lemma li_wpe_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPexp (Manyop op es ann) {{ Φ }}.
  Proof. apply: wpe_manyop. Qed.

  Lemma li_wpe_unop op e Φ ann:
    WPexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}} -∗
    WPexp (Unop op e ann) {{ Φ }}.
  Proof. apply: wpe_unop. Qed.

  Lemma li_wpe_binop op e1 e2 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPexp (Binop op e1 e2 ann) {{ Φ }}.
  Proof. apply: wpe_binop. Qed.

  Lemma li_wpe_ite e1 e2 e3 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, WPexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }} -∗
    WPexp (Ite e1 e2 e3 ann) {{ Φ }}.
  Proof. apply: wpe_ite. Qed.
End instances.

(* This seems to have to live outside of the section because of hint lifetimes? *)
(* #[ global ] Hint Extern 10 (FindHypEqual FICMapstoSemantic (_ ↦ₘ _) (_ ↦ₘ _) _) => *)
(* ( apply tac_mapsto_eq; done) : typeclass_instances. *)

#[ global ] Hint Extern 10 (FindHypEqual FICMapstoSemantic (_ ↦ₘ _) (_ ↦ₘ _) _) =>
  ( apply tac_mapsto_eq; bv_solve) : typeclass_instances.

(* TODO: upstream? *)
Ltac liLetBindHint :=
  idtac;
  match goal with
  | |- envs_entails ?Δ (let_bind_hint ?x ?f) =>
    let H := fresh "LET" in
    lazymatch x with
    | Val_Bits (bv_to_bvn ?y) =>
      lazymatch y with
      | _ _ =>
        pose (H := y);
        change (envs_entails Δ (f (Val_Bits (bv_to_bvn H)))); cbn beta
      | _ => (* No application, probably just another let binding. Don't create a new one.  *)
        change (envs_entails Δ (f x)); cbn beta
      end
    | Val_Bool ?y =>
      lazymatch y with
      | _ _ =>
        pose (H := y);
        change (envs_entails Δ (f (Val_Bool H))); cbn beta
      | _ => (* No application, probably just another let binding. Don't create a new one.  *)
        change (envs_entails Δ (f x)); cbn beta
      end
    end
  end.

Ltac liAAsm :=
  lazymatch goal with
  | |- envs_entails ?Δ (WPasm ?es) =>
    lazymatch es with
    | [] => notypeclasses refine (tac_fast_apply (li_wp_next_instr) _)
    | ?e :: _ =>
      lazymatch e with
      | ReadReg _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_reg _ _ _ _ _) _)
      | WriteReg _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_reg _ _ _ _ _) _)
      | BranchAddress _ _ => notypeclasses refine (tac_fast_apply (li_wp_branch_address _ _ _) _)
      | ReadMem _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_mem _ _ _ _ _ _ _ _) _)
      | WriteMem _ _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_mem _ _ _ _ _ _ _ _ _) _)
      | Smt (DeclareConst _ (Ty_BitVec _)) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bv _ _ _ _) _)
      | Smt (DeclareConst _ Ty_Bool) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bool _ _ _) _)
      | Smt (DefineConst _ _) _ => notypeclasses refine (tac_fast_apply (li_wp_define_const _ _ _ _) _)
      | Smt (Assert _) _ => notypeclasses refine (tac_fast_apply (li_wp_assert _ _ _) _)
      end
    | ?def => first [
                 iEval (unfold def)
               | fail "liAAsm: unknown asm" es
               ]
    end
  | |- envs_entails ?Δ (instr_pre' _ _ _) =>
    notypeclasses refine (tac_fast_apply (li_instr_pre _ _ _) _)
  end.

Ltac liAExp :=
  lazymatch goal with
  | |- envs_entails ?Δ (wp_exp ?e _) =>
    lazymatch e with
    | Val _ _ => notypeclasses refine (tac_fast_apply (li_wpe_val _ _ _) _)
    | Manyop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_manyop _ _ _ _) _)
    | Unop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_unop _ _ _ _) _)
    | Binop _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_binop _ _ _ _ _) _)
    | Ite _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_ite _ _ _ _ _) _)
    | _ => fail "liAExp: unknown exp" e
    end
  end.


Ltac liAStep :=
 liEnforceInvariantAndUnfoldInstantiatedEvars;
 first [
    liAAsm
  | liAExp
  | liStep
  | liLetBindHint
]; liSimpl.
