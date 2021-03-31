From iris.proofmode Require Import coq_tactics reduction.
From isla Require Export lifting.
From refinedc.lithium Require Export lithium tactics.
Set Default Proof Using "Type".

(** * Registering extensions *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac normalize_tac ::= normalize_autorewrite.

Section instances.
  Context `{!islaG Σ} `{!threadG}.

  Global Instance instr_intro_pers i a : IntroPersistent (instr a i) (instr a i).
  Proof. constructor. iIntros "#$". Qed.

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


  Lemma li_wp_next_instr:
    (∃ nPC bPC_changed, "_PC" ↦ᵣ Val_Bits nPC ∗ "__PC_changed" ↦ᵣ Val_Bool bPC_changed ∗
     ∃ a newPC newPC_changed, ⌜next_pc nPC bPC_changed = Some (a, newPC, newPC_changed)⌝ ∗
     ∃ ins, instr a ins ∗
     match ins with
     | Some ts =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, "_PC" ↦ᵣ newPC -∗ "__PC_changed" ↦ᵣ newPC_changed -∗ WPasm t
     | None =>
       ∃ κs, spec_trace κs ∗ ⌜hd_error κs = Some (SInstrTrap a)⌝
                              ∗ True
     end
    ) -∗
    WPasm [].
  Proof.
    iDestruct 1 as (??) "(?&?&Hwp)".
    iDestruct "Hwp" as (???? ins) "[Hi Hwp]".
    case_match.
    - iDestruct "Hwp" as (?) "Hl".
      iApply (wp_next_instr with "[$] [$] [$]") => //.
      iIntros (i Hi) "? ?".
      iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
      iApply ("Hwp" with "[$] [$]").
    - iDestruct "Hwp" as (?) "(?&%&?)".
      iApply (wp_next_instr_extern with "[$] [$] [$] [$]") => //.
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
    (∀ n, WPasm ((subst_event v (Val_Bits [BV{b} n])) <$> es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :: es).
  Proof. apply: wp_declare_const_bv. Qed.

  Lemma li_wp_define_const n es ann e:
    WPexp e {{ v, WPasm ((subst_event n v) <$> es) }} -∗
    WPasm (Smt (DefineConst n e) ann :: es).
  Proof. apply: wp_define_const. Qed.

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
      | Smt (DeclareConst _ (Ty_BitVec _)) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bv _ _ _ _) _)
      | Smt (DefineConst _ _) _ => notypeclasses refine (tac_fast_apply (li_wp_define_const _ _ _ _) _)
      end
    | ?def => first [
                 iEval (unfold def)
               | fail "liAAsm: unknown asm" es
               ]
    end
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
]; liSimpl.